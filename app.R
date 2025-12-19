# =========================================================
# app.R — Merging Airport Files (Daily-only) — Upgraded
# - Input validation & inline guidance (blocking warnings)
# - "Different for Four Surveys and Above (≥4)" + High% slider (default 100%)
# - Plan parsing by column positions: A=Route, B=Total desired, C=Collected
# - Tabs ordered Sun → Sat; legend bullet points for Days of Operation
# - Require Concourse and Flight Type in acronym files (no blanks)
# - Parameters sheet in export; Missing Mappings sheet (only if needed)
# - Extra header robustness (NBSP trimming/aliases) & perf tweaks
# =========================================================

options(shiny.maxRequestSize = 200 * 1024^2)

suppressPackageStartupMessages({
  library(shiny)
  library(readxl)
  library(dplyr)
  library(tidyr)
  library(stringr)
  library(purrr)
  library(openxlsx)
  library(tibble)
  library(lubridate)
  library(DT)
})

# ---------------------- Config ----------------------
ACRONYM_PATHS <- c(".", "MergedAirportFiles", "MergingAirportFiles", "Merging_Airport_Files")
AIRLINES_FILE     <- "Acronyms for Airlines.xlsx"
DESTINATIONS_FILE <- "Acronyms for Airport Destinations.xlsx"

# ---------------------- Helpers ----------------------
`%||%` <- function(a, b) if (!is.null(a) && length(a) > 0) a else b
nzint <- function(x) { x <- suppressWarnings(as.integer(x)); ifelse(is.na(x), 0L, x) }
safe_trim <- function(x) trimws(gsub("\u00A0", " ", as.character(x)))
# Parse numbers from mixed/dirty cells like "1,234", "3 of 10", "4/4", " 7 ", "—"
parse_numeric_relaxed <- function(x) {
  # Fast path for numeric input
  out <- suppressWarnings(as.numeric(x))
  needs_fix <- is.na(out)
  
  if (any(needs_fix)) {
    sx <- safe_trim(as.character(x))
    
    # If value looks like "3/10" or "3 of 10", keep the first number
    sx <- ifelse(
      grepl("^\\s*\\d+\\s*(/|of)\\s*\\d+\\s*$", tolower(sx)),
      sub("^\\s*(\\d+)\\s*(/|of).*$", "\\1", tolower(sx)),
      sx
    )
    
    # Strip everything except digits, minus, and decimal point (handles "1,234", "4*" etc.)
    sx2 <- gsub("[^0-9.-]", "", sx)
    sx2[nchar(sx2) == 0] <- NA_character_
    
    out2 <- suppressWarnings(as.numeric(sx2))
    out[needs_fix] <- out2[needs_fix]
  }
  
  out
}

drop_unnamed_blank_cols <- function(df) {
  if (is.null(df) || !is.data.frame(df) || !ncol(df)) return(df)
  nm <- names(df)
  bad <- grepl("^Unnamed", nm) | grepl("^\\.\\.\\.[0-9]+$", nm)
  all_blank <- vapply(df, function(col) {
    all(is.na(col) | safe_trim(col) == "")
  }, logical(1))
  keep <- !(bad & all_blank)
  df[, keep, drop = FALSE]
}

trim_names <- function(df) { names(df) <- safe_trim(names(df)); df }

read_excel_simple <- function(path, sheet = NULL){
  df <- suppressMessages(readxl::read_excel(path, sheet = sheet))
  drop_unnamed_blank_cols(trim_names(df))
}

find_file <- function(fname, paths = ACRONYM_PATHS) {
  hits <- file.path(paths, fname)
  hit <- hits[file.exists(hits)]
  if (length(hit)) hit[1] else fname
}

# Convert many kinds of inputs to canonical "HH:MM" 24h
parse_time_hhmm <- function(x) {
  parse_one <- function(xx) {
    if (is.null(xx) || length(xx) == 0) return(NA_character_)
    if (inherits(xx, c("POSIXct","POSIXlt"))) {
      hh <- lubridate::hour(xx); mm <- lubridate::minute(xx)
      if (is.na(hh) || is.na(mm)) return(NA_character_)
      return(sprintf("%02d:%02d", hh %% 24L, mm %% 60L))
    }
    if (is.numeric(xx) && is.finite(xx)) {
      mins <- as.integer(round((xx %% 1) * 1440))
      hh <- (mins %/% 60) %% 24; mm <- mins %% 60
      return(sprintf("%02d:%02d", hh, mm))
    }
    s <- tryCatch(safe_trim(xx), error = function(e) "")
    if (!nzchar(s) || is.na(s) || identical(tolower(s), "na")) return(NA_character_)
    # AM/PM
    if (grepl("(?i)\\b(am|pm)\\b", s, perl = TRUE)) {
      t <- try(as.POSIXlt(s, format = "%I:%M %p", tz = "UTC"), silent = TRUE)
      if (!inherits(t, "try-error") && !is.na(t$hour)) {
        return(sprintf("%02d:%02d", as.integer(t$hour) %% 24L, as.integer(t$min) %% 60L))
      }
      t2 <- try(as.POSIXlt(s, format = "%I %p", tz = "UTC"), silent = TRUE)
      if (!inherits(t2, "try-error") && !is.na(t2$hour)) {
        return(sprintf("%02d:%02d", as.integer(t2$hour) %% 24L, 0L))
      }
    }
    # 24h H:MM / HH:MM
    m <- regexpr("(\\d{1,2}):(\\d{2})", s, perl = TRUE)
    if (!is.na(m) && m > 0) {
      frag <- substr(s, m, m + attr(m, "match.length") - 1)
      hh <- suppressWarnings(as.integer(sub(":.*", "", frag)))
      mm <- suppressWarnings(as.integer(sub(".*:", "", frag)))
      if (!is.na(hh) && !is.na(mm) && hh >= 0 && hh <= 23 && mm >= 0 && mm <= 59) {
        return(sprintf("%02d:%02d", hh, mm))
      }
    }
    # raw digits 0815 / 915
    s2 <- gsub("[^0-9]", "", s)
    if (nzchar(s2) && nchar(s2) <= 4) {
      s2 <- stringr::str_pad(s2, 4, pad = "0")
      hh <- suppressWarnings(as.integer(substr(s2, 1, 2)))
      mm <- suppressWarnings(as.integer(substr(s2, 3, 4)))
      if (!is.na(hh) && !is.na(mm) && hh >= 0 && hh <= 23 && mm >= 0 && mm <= 59) {
        return(sprintf("%02d:%02d", hh, mm))
      }
      if (!is.na(hh) && !is.na(mm) && hh == 24 && mm == 0) {
        return("00:00")
      }
    }
    NA_character_
  }
  vapply(x, parse_one, FUN.VALUE = character(1))
}

hhmm_to_min <- function(hhmm) {
  s <- as.character(hhmm)
  ifelse(!is.na(s) & grepl("^\\d{2}:\\d{2}$", s),
         as.integer(substr(s,1,2)) * 60L + as.integer(substr(s,4,5)),
         NA_integer_)
}

date_label <- function(d) sprintf("%d/%d", lubridate::month(d), lubridate::mday(d))

# ---------------------- Load Acronyms (strict) ----------------------
load_airline_acronyms <- function() {
  path <- find_file(AIRLINES_FILE)
  validate(need(file.exists(path),
                paste0("Missing required file: '", AIRLINES_FILE, "'. Place it next to app.R or add its folder to ACRONYM_PATHS.")))
  df <- read_excel_simple(path)
  nms <- tolower(names(df))
  acro_col <- names(df)[which(str_detect(nms, "^acronym$|\\bcode\\b|iata"))[1]]
  name_col <- names(df)[which(str_detect(nms, "^airline$|carrier|name"))[1]]
  conc_col <- names(df)[which(str_detect(nms, "concourse|terminal"))[1]]
  validate(need(!is.na(acro_col) && !is.na(name_col) && !is.na(conc_col),
                "Airlines acronyms must include Code/IATA, Airline Name, and Concourse columns."))
  
  ac <- df %>%
    transmute(
      Acronym   = toupper(safe_trim(.data[[acro_col]])),
      Airline   = safe_trim(.data[[name_col]]),
      Concourse = safe_trim(.data[[conc_col]])
    ) %>%
    filter(nzchar(Acronym) & nzchar(Airline) & nzchar(Concourse))
  
  validate(need(nrow(ac) > 0, "Airlines acronyms has no valid (non-blank) rows for required fields."))
  validate(need(all(nzchar(ac$Acronym)) && all(nzchar(ac$Airline)) && all(nzchar(ac$Concourse)),
                "Airlines acronyms contains blank values; Concourse is required for all rows."))
  
  list(
    name_map = setNames(ac$Airline, ac$Acronym),
    conc_map = setNames(ac$Concourse, ac$Acronym)
  )
}

load_dest_acronyms <- function() {
  path <- find_file(DESTINATIONS_FILE)
  validate(need(file.exists(path),
                paste0("Missing required file: '", DESTINATIONS_FILE, "'. Place it next to app.R or add its folder to ACRONYM_PATHS.")))
  df <- read_excel_simple(path)
  nms <- tolower(names(df))
  code_col <- names(df)[which(str_detect(nms, "^acronym$|\\bcode\\b|iata"))[1]]
  name_col <- names(df)[which(str_detect(nms, "destination|name"))[1]]
  type_col <- names(df)[which(str_detect(nms, "flight type|type|intl|international|domestic"))[1]]
  validate(need(!is.na(code_col) && !is.na(name_col) && !is.na(type_col),
                "Destinations acronyms must include Code/IATA, Destination Name, and Flight Type columns."))
  
  df2 <- df %>%
    transmute(
      DestCode  = toupper(safe_trim(.data[[code_col]])),
      DestName  = safe_trim(.data[[name_col]]),
      FlightType = case_when(
        tolower(safe_trim(.data[[type_col]])) %in% c("intl","international") ~ "International",
        tolower(safe_trim(.data[[type_col]])) %in% c("dom","domestic") ~ "Domestic",
        TRUE ~ NA_character_
      )
    ) %>%
    filter(nzchar(DestCode) & nzchar(DestName) & nzchar(FlightType))
  
  validate(need(nrow(df2) > 0, "Destinations acronyms has no valid (non-blank) rows for required fields."))
  validate(need(all(nzchar(df2$DestCode)) && all(nzchar(df2$DestName)) && all(nzchar(df2$FlightType)),
                "Destinations acronyms contains blank values; Flight Type is required for all rows."))
  
  df2
}

acr_air  <- load_airline_acronyms()
acr_dest <- load_dest_acronyms()

# ---------------------- Plan parsing (position-based with ≥4 rule) ----------------------
parse_plan_sheet <- function(df, pct_base = 0.85, pct_high = 1.00, high_threshold = 4L) {
  df <- drop_unnamed_blank_cols(df)
  validate(need(ncol(df) >= 3, paste0(
    "Plan sheet must have at least 3 columns:\n",
    "  Col A: Airline-Destination (e.g., DL-ATL)\n",
    "  Col B: Total desired (number)\n",
    "  Col C: Collected (number)\n"
  )))
  
  combo <- as.character(df[[1]])
  # Primary: position-based B (Total), C (Collected)
  tot_raw  <- df[[2]]
  coll_raw <- df[[3]]
  
  # Position-only plan parsing: Col C is *always* the Collected column.
  # We intentionally ignore header names here.
  
  # Robust numeric parsing (handles "1,234", "3/10", "3 of 10", "—", etc.)
  tot  <- parse_numeric_relaxed(tot_raw)
  coll <- parse_numeric_relaxed(coll_raw)
  
  okB <- mean(is.na(tot)) < 0.5
  okC <- mean(is.na(coll)) < 0.5
  validate(need(okB && okC,
                paste0(
                  "Plan format issue: Columns B (Total desired) and C (Collected) must be mostly numeric.\n",
                  "Tips: avoid text like '3 of 10'; if present, this app now reads the first number."
                )))
  
  code <- toupper(trimws(sub("\\-.*$", "", combo)))
  dest <- toupper(trimws(sub("^.*?\\-", "", combo)))
  
  tot2  <- pmax(0L, nzint(tot))
  coll2 <- pmax(0L, nzint(coll))
  # Never allow collected to exceed total (guards against bad cells)
  coll2 <- pmin(coll2, tot2)
  
  goal_base <- ceiling(pct_base * tot2)
  goal_high <- ceiling(pct_high * tot2)
  use_high  <- tot2 >= as.integer(high_threshold)
  goal      <- ifelse(use_high, goal_high, goal_base)
  
  assigned  <- pmax(0L, goal - coll2)
  assigned  <- pmin(assigned, pmax(0L, tot2 - coll2))  # never exceed remaining
  
  AirlineName <- dplyr::coalesce(acr_air$name_map[code], code)
  
  tibble(
    `Airline Code`      = code,
    Airline             = AirlineName,
    `Destination Code`  = dest,
    `Assigned Surveys`  = assigned
  ) %>%
    filter(nzchar(`Airline Code`) & nzchar(`Destination Code`)) %>%
    group_by(`Airline Code`, Airline, `Destination Code`) %>%
    summarise(`Assigned Surveys` = sum(`Assigned Surveys`, na.rm = TRUE), .groups = "drop") %>%
    mutate(`Unique Route Number` = dplyr::row_number())
}

parse_plan <- function(path, pct_base = 0.85, pct_high = 1.00, high_threshold = 4L) {
  sheets <- tryCatch(readxl::excel_sheets(path), error = function(e) character(0))
  if (!length(sheets)) {
    df <- read_excel_simple(path)
    return(parse_plan_sheet(df, pct_base, pct_high, high_threshold))
  }
  parts <- lapply(sheets, function(sh) {
    df <- read_excel_simple(path, sheet = sh)
    tryCatch(parse_plan_sheet(df, pct_base, pct_high, high_threshold),
             error = function(e) tibble())
  })
  bind_rows(parts)
}

# ---------------------- DAILY workbook reader (robust headers) ----------------------
.find_header_row_relaxed <- function(df0) {
  max_check <- min(60L, nrow(df0))
  for (r in seq_len(max_check)) {
    row_txt <- tolower(safe_trim(unlist(df0[r, ], use.names = FALSE)))
    if (!any(nzchar(row_txt))) next
    has_hub <- any(row_txt %in% c("hub time","hubtime","hub_time"))
    has_dst <- any(row_txt %in% c("dest","destination"))
    has_al  <- any(row_txt %in% c("mkt al","mktal","mkt_al","airline","carrier"))
    has_flt <- any(row_txt %in% c("flight","flight #","flight number","flt","#","flight no","flightno","flight no."))
    if ((has_hub + has_dst + has_al + has_flt) >= 3) return(r)
  }
  NA_integer_
}

.parse_daily_sheet_v3 <- function(path, sh, year) {
  raw <- suppressMessages(readxl::read_excel(path, sheet = sh, col_names = FALSE))
  if (is.null(raw) || !nrow(raw)) return(NULL)
  
  hdr_row <- .find_header_row_relaxed(raw)
  if (is.na(hdr_row) && nrow(raw) >= 4) hdr_row <- 4L
  if (is.na(hdr_row)) return(NULL)
  
  hdr <- as.character(unlist(raw[hdr_row, ], use.names = FALSE))
  hdr <- safe_trim(hdr)
  hdr[!nzchar(hdr) | is.na(hdr)] <- paste0("...", seq_len(sum(!nzchar(hdr) | is.na(hdr))))
  df  <- raw[(hdr_row + 1):nrow(raw), , drop = FALSE]
  names(df) <- hdr
  df <- drop_unnamed_blank_cols(trim_names(df))
  if (!ncol(df)) return(NULL)
  
  # Tab name to date (accept m-d, m_d, m.d, m/d)
  pat <- "^(\\d{1,2})[-_/\\.](\\d{1,2})$"
  if (!grepl(pat, sh)) return(NULL)
  m <- as.integer(sub(pat, "\\1", sh, perl = TRUE))
  d <- as.integer(sub(pat, "\\2", sh, perl = TRUE))
  dep_date <- suppressWarnings(as.Date(sprintf("%04d-%02d-%02d", as.integer(year), m, d)))
  if (is.na(dep_date)) return(NULL)
  
  nmsl <- tolower(names(df))
  pick_last <- function(cands) {
    hits <- which(nmsl %in% tolower(cands))
    if (length(hits)) max(hits) else NA_integer_
  }
  safe_get  <- function(df, idx) {
    if (!is.na(idx) && idx >= 1 && idx <= ncol(df)) df[[idx]] else NA
  }
  
  hub_idx  <- pick_last(c("hub time","hubtime","hub_time","Hub Time","HubTime","Hub_Time"))
  dest_idx <- pick_last(c("dest","destination","Dest","Destination"))
  al_idx   <- pick_last(c("mkt al","mktal","mkt_al","airline","carrier","Mkt Al","MktAl","Mkt_Al","Airline","Carrier"))
  flt_idx  <- pick_last(c("flight","#","flight #","flight number","flightno","flight no","flt",
                          "Flight","#","Flight #","Flight Number","FlightNo","Flight No","Flt","Flight No."))
  
  by_name <- tibble(
    `Departure Time`   = safe_get(df, hub_idx),
    `Destination Code` = safe_get(df, dest_idx),
    `Airline Code`     = safe_get(df, al_idx),
    `Flight #`         = safe_get(df, flt_idx)
  )
  
  by_pos <- NULL
  if (ncol(df) >= 15) {
    by_pos <- tibble(
      `Departure Time`   = df[[8]],
      `Destination Code` = df[[10]],
      `Airline Code`     = df[[12]],
      `Flight #`         = df[[13]]
    )
  }
  
  pick <- function(x) {
    if (is.null(x)) return(NULL)
    has_any <- with(x, any(!is.na(`Departure Time`) |
                             nzchar(as.character(`Destination Code`)) |
                             nzchar(as.character(`Airline Code`)) |
                             nzchar(as.character(`Flight #`))))
    if (isTRUE(has_any)) x else NULL
  }
  
  df2 <- pick(by_name)
  if (is.null(df2)) df2 <- pick(by_pos)
  if (is.null(df2)) return(NULL)
  
  df2 %>%
    mutate(
      `Departure Time`   = parse_time_hhmm(`Departure Time`),
      `Destination Code` = toupper(trimws(as.character(`Destination Code`))),
      `Airline Code`     = toupper(trimws(as.character(`Airline Code`))),
      `Flight #`         = trimws(as.character(`Flight #`)),
      dep_date           = dep_date
    ) %>%
    filter(!is.na(`Departure Time`) |
             nzchar(`Destination Code`) |
             nzchar(`Airline Code`) |
             nzchar(`Flight #`))
}

read_daily_calendar <- function(path, year) {
  shs <- readxl::excel_sheets(path)
  pat <- "^(\\d{1,2})[-_/\\.](\\d{1,2})$"
  keep <- shs[grepl(pat, shs)]
  validate(need(length(keep) > 0, "No daily tabs named like '9-2' were found."))
  
  parts <- lapply(keep, function(sh) .parse_daily_sheet_v3(path, sh, year))
  daily <- dplyr::bind_rows(parts)
  validate(need(nrow(daily) > 0, "Daily workbook parsed to 0 rows after relaxed detection."))
  
  daily %>%
    mutate(
      Airline   = dplyr::coalesce(acr_air$name_map[`Airline Code`], `Airline Code`),
      Concourse = dplyr::coalesce(acr_air$conc_map[`Airline Code`], NA_character_)
    ) %>%
    left_join(acr_dest, by = c("Destination Code" = "DestCode")) %>%
    rename(`Destination` = DestName, `Flight Type` = FlightType) %>%
    mutate(
      DayName = factor(weekdays(dep_date),
                       levels = c("Sunday","Monday","Tuesday","Wednesday","Thursday","Friday","Saturday"))
    ) %>%
    select(dep_date, DayName, Airline, `Airline Code`, Concourse,
           `Destination`, `Destination Code`, `Flight #`, `Departure Time`, `Flight Type`)
}

# ---------------------- UI ----------------------
ui <- fluidPage(
  titlePanel("Merging Airport Files — Daily Calendar"),
  tags$head(
    tags$style(HTML("
      #busy-overlay{position:fixed;inset:0;display:none;align-items:center;justify-content:center;background:rgba(255,255,255,.82);z-index:9999;}
      .shiny-busy #busy-overlay{display:flex;}
      #busy-box{background:#f7f7f7;border:1px solid #ddd;padding:16px 22px;border-radius:10px;font-weight:600;box-shadow:0 6px 20px rgba(0,0,0,.12);}
      .summary-grid{display:grid;grid-template-columns:1fr 1fr;gap:14px;max-width:720px;}
      .tile{border-radius:10px;padding:12px 14px;border:1px solid #e6e6e6;}
      .bg-gray{background:#f7f7f7;}
      .bg-green{background:#eef8ef;}
      .bg-red{background:#fdeeee;}
      .lbl{font-weight:400;}
      .num{font-weight:700;font-size:1.5rem;margin-left:6px;}
      .warn{background:#fff3cd;border:1px solid #ffeeba;padding:10px 12px;border-radius:8px;margin-bottom:12px;}
      .legend-box{background:#f7f7f7;border:1px solid #e6e6e6;padding:8px 12px;border-radius:8px;margin-top:8px;color:#555;}
      .legend-box ul{margin:0 0 0 18px;padding:0;}
    "))
  ),
  div(id = "busy-overlay", div(id = "busy-box", "Merging…")),
  sidebarLayout(
    sidebarPanel(width = 4,
                 fileInput("plan",  "ASQ Survey Plan (xlsx)",   accept = ".xlsx"),
                 fileInput("daily", "Daily Flight Schedule (xlsx)", accept = ".xlsx"),
                 numericInput("year_in", "Year", value = as.integer(format(Sys.Date(), "%Y")), min = 2020, max = 2100, step = 1),
                 sliderInput("pct_required", "Minimum % of Each Survey Route Required", min = 0, max = 100, value = 85, step = 1, post = "%"),
                 checkboxInput("hi_rule", "Different for Four Surveys and Above (≥4)", value = FALSE),
                 conditionalPanel(
                   condition = "input.hi_rule == true",
                   sliderInput("pct_high", "Minimum % of Each Survey Route Required when Target ≥ 4", min = 0, max = 100, value = 100, step = 1, post = "%")
                 ),
                 actionButton("merge", "Merge"),
                 tags$hr(),
                 div(class = "legend-box",
                     tags$div(tags$strong("Days of Operation:")),
                     tags$ul(
                       tags$li(HTML("<b>1</b>=Sun … <b>7</b>=Sat")),
                       tags$li(HTML("<b>.</b> = not operating"))
                     )
                 ),
                 downloadButton("download_xlsx", "Download Calendar Workbook")
    ),
    mainPanel(
      uiOutput("tabs_ui")
    )
  )
)

# ---------------------- Server ----------------------
server <- function(input, output, session) {
  
  # Infer year from daily filename if possible
  observeEvent(input$daily, {
    y_def <- as.integer(format(Sys.Date(), "%Y"))
    if (!isTruthy(input$daily$name)) {
      updateNumericInput(session, "year_in", value = y_def)
      return()
    }
    nm <- input$daily$name
    y <- suppressWarnings(as.integer(stringr::str_extract(nm, "(?<!\\d)(20\\d{2})(?!\\d)")))
    if (!is.na(y)) {
      updateNumericInput(session, "year_in", value = y)
      return()
    }
    y2 <- suppressWarnings(as.integer(stringr::str_extract(nm, "(?i)(20\\d{2})")))
    updateNumericInput(session, "year_in", value = y2 %||% y_def)
  }, ignoreInit = TRUE)
  
  # Daily
  daily_df <- reactive({
    req(input$daily, input$plan, input$year_in)
    read_daily_calendar(input$daily$datapath, year = as.integer(input$year_in))
  })
  
  # Parse plan with base/high percentages and threshold
  parse_plan_reactive <- eventReactive(input$merge, {
    req(input$plan)
    pct_base <- as.numeric(input$pct_required)
    if (is.na(pct_base)) pct_base <- 85
    pct_base <- pmax(0, pmin(100, pct_base)) / 100
    
    use_high <- isTRUE(input$hi_rule)
    pct_high <- if (use_high) {
      pmax(0, pmin(100, as.numeric(input$pct_high) %||% 100)) / 100
    } else {
      pct_base
    }
    
    parse_plan(input$plan$datapath, pct_base = pct_base, pct_high = pct_high, high_threshold = 4L)
  })
  
  plan_routes <- reactive({
    req(parse_plan_reactive())
    parse_plan_reactive() %>% filter(nzint(`Assigned Surveys`) > 0)
  })
  
  # Month for filename
  month_from_daily <- reactive({
    req(input$daily)
    shs <- readxl::excel_sheets(input$daily$datapath)
    pat <- "^(\\d{1,2})[-_/\\.](\\d{1,2})$"
    mm <- as.integer(sub(pat, "\\1", shs[grepl(pat, shs)], perl = TRUE))
    mm <- mm[!is.na(mm)]
    if (length(mm)) {
      as.integer(names(sort(table(mm), decreasing = TRUE))[1])
    } else {
      as.integer(format(Sys.Date(), "%m"))
    }
  })
  
  # Merge calendar
  merged_calendar <- reactive({
    daily  <- daily_df()
    routes <- plan_routes()
    daily_need <- daily %>%
      inner_join(
        routes %>% select(`Airline Code`, `Destination Code`, `Assigned Surveys`, `Unique Route Number`),
        by = c("Airline Code","Destination Code")
      ) %>%
      mutate(
        Airline = dplyr::coalesce(acr_air$name_map[`Airline Code`], `Airline Code`)
      )
    list(calendar = daily_need)
  })
  
  # Encode days mask 1..7 where 1=Sun
  encode_days <- function(day_digits) {
    present <- unique(as.character(day_digits))
    paste0(
      sapply(1:7, function(i) {
        if (as.character(i) %in% present) as.character(i) else "."
      }),
      collapse = ""
    )
  }
  
  routes_remaining_all <- reactive({
    routes <- plan_routes()
    if (!nrow(routes)) return(tibble())
    
    routes_enriched <- routes %>%
      mutate(
        Airline   = dplyr::coalesce(Airline, acr_air$name_map[`Airline Code`], `Airline Code`),
        Concourse = dplyr::coalesce(acr_air$conc_map[`Airline Code`], NA_character_)
      ) %>%
      left_join(
        acr_dest %>% transmute(`Destination Code` = DestCode,
                               Destination = DestName,
                               `Flight Type` = FlightType),
        by = "Destination Code"
      )
    
    dd <- daily_df()
    if (nrow(dd)) {
      day_to_digit <- c(Sunday="1", Monday="2", Tuesday="3", Wednesday="4", Thursday="5", Friday="6", Saturday="7")
      days_map <- dd %>%
        mutate(day_digit = unname(day_to_digit[as.character(DayName)])) %>%
        group_by(`Airline Code`, `Destination Code`) %>%
        summarise(`Days of Operation` = encode_days(day_digit), .groups = "drop")
    } else {
      days_map <- tibble(`Airline Code`=character(0), `Destination Code`=character(0), `Days of Operation`=character(0))
    }
    
    routes_enriched %>%
      left_join(days_map, by = c("Airline Code","Destination Code")) %>%
      mutate(`Days of Operation` = ifelse(is.na(`Days of Operation`), ".......", `Days of Operation`)) %>%
      select(`Unique Route Number`, Airline, Concourse, Destination, `Assigned Surveys`, `Flight Type`,
             `Airline Code`, `Destination Code`, `Days of Operation`) %>%
      arrange(`Unique Route Number`, Airline, `Destination Code`)
  })
  
  required_no_flights <- reactive({
    routes <- plan_routes()
    cal <- merged_calendar()$calendar
    if (!nrow(routes)) return(tibble())
    have <- cal %>% distinct(`Airline Code`, `Destination Code`)
    missing <- anti_join(routes, have, by = c("Airline Code","Destination Code"))
    
    missing %>%
      left_join(
        acr_dest %>%
          transmute(`Destination Code` = DestCode,
                    Destination = DestName,
                    `Flight Type` = FlightType),
        by = "Destination Code"
      ) %>%
      transmute(
        Airline,
        Destination,
        `Assigned Surveys`,
        `Flight Type`,
        `Airline Code`,
        `Destination Code`,
        `Unique Route Number`
      ) %>%
      arrange(`Unique Route Number`, Airline, Destination)
  })
  
  # Missing mappings — now ONLY based on codes present in the PLAN (per your request)
  missing_mappings <- reactive({
    routes <- try(plan_routes(), silent = TRUE)
    if (inherits(routes, "try-error") || is.null(routes) || !nrow(routes)) return(tibble())
    
    seen_air <- unique(na.omit(routes$`Airline Code`))
    seen_dst <- unique(na.omit(routes$`Destination Code`))
    
    miss_air <- setdiff(seen_air, names(acr_air$name_map))
    miss_dst <- setdiff(seen_dst, acr_dest$DestCode)
    
    if (!length(miss_air) && !length(miss_dst)) return(tibble())
    
    make_rows <- function(type, codes) {
      if (!length(codes)) return(tibble())
      tibble(Type = type, Code = codes, Where = "plan", Occurrences = NA_integer_)
    }
    
    bind_rows(
      make_rows("AirlineCode", miss_air),
      make_rows("DestinationCode", miss_dst)
    ) %>% arrange(Type, Code)
  })
  
  # Summary counts
  summary_counts <- reactive({
    routes <- plan_routes()
    cal    <- merged_calendar()$calendar
    total_routes <- n_distinct(routes$`Unique Route Number`)
    found_routes <- n_distinct(cal$`Unique Route Number`)
    not_found    <- total_routes - found_routes
    total_needed <- sum(routes$`Assigned Surveys`, na.rm = TRUE)
    able_alloc <- cal %>%
      group_by(`Unique Route Number`) %>%
      summarise(alloc = min(first(`Assigned Surveys`), n()), .groups = "drop") %>%
      summarise(sum_alloc = sum(alloc, na.rm = TRUE), .groups = "drop") %>%
      pull(sum_alloc)
    unable_alloc <- total_needed - able_alloc
    tibble(
      `Total Routes with Assigned Surveys`   = total_routes,
      `Total Required Surveys Remaining`     = total_needed,
      `Routes Found in Flight Schedule`      = found_routes,
      `Surveys Able to be Allocated`         = able_alloc,
      `Routes Not Found in Flight Schedule`  = not_found,
      `Surveys Unable to be Allocated`       = unable_alloc
    )
  })
  
  # ---------- Tabs UI (Sun..Sat + tables + warnings) ----------
  output$tabs_ui <- renderUI({
    req(input$plan, input$daily, input$merge)
    counts <- summary_counts()
    warn_mm <- try(missing_mappings(), silent = TRUE)
    warn_ui <- NULL
    if (!inherits(warn_mm, "try-error") && nrow(warn_mm) > 0) {
      ex_items <- paste0(warn_mm$Type, ": ", warn_mm$Code, " (", warn_mm$Where, ")")
      ex <- paste(head(ex_items, 5), collapse = "; ")
      warn_ui <- div(class = "warn",
                     paste0("Missing acronym mappings detected in the plan. e.g., ", ex))
    }
    
    # SWAPPED columns per your request:
    # Left column now shows *Required/Allocable/Unable*, Right column shows *Routes/Found/Not Found*
    summary_ui <- tagList(
      warn_ui,
      div(class = "summary-grid",
          div(class="tile bg-gray",
              span(class="lbl", "Total Required Surveys Remaining:"),
              span(class="num", counts$`Total Required Surveys Remaining`)
          ),
          div(class="tile bg-gray",
              span(class="lbl", "Total Routes with Assigned Surveys:"),
              span(class="num", counts$`Total Routes with Assigned Surveys`)
          ),
          div(class="tile bg-green",
              span(class="lbl", "Surveys Able to be Allocated:"),
              span(class="num", counts$`Surveys Able to be Allocated`)
          ),
          div(class="tile bg-green",
              span(class="lbl", "Routes Found in Flight Schedule:"),
              span(class="num", counts$`Routes Found in Flight Schedule`)
          ),
          div(class="tile bg-red",
              span(class="lbl", "Surveys Unable to be Allocated:"),
              span(class="num", counts$`Surveys Unable to be Allocated`)
          ),
          div(class="tile bg-red",
              span(class="lbl", "Routes Not Found in Flight Schedule:"),
              span(class="num", counts$`Routes Not Found in Flight Schedule`)
          )
      )
    )
    
    tabs <- list(tabPanel("Summary", br(), summary_ui, br()))
    
    cal <- merged_calendar()$calendar
    if (nrow(cal)) {
      cal <- cal %>%
        mutate(
          Airline   = dplyr::coalesce(acr_air$name_map[`Airline Code`], `Airline Code`),
          DateLabel = date_label(dep_date),
          DepMin    = hhmm_to_min(`Departure Time`)
        ) %>%
        arrange(dep_date, DepMin, Airline, `Destination Code`)
    }
    
    day_names <- c("Sunday","Monday","Tuesday","Wednesday","Thursday","Friday","Saturday")
    for (dn in day_names) {
      short <- substr(dn, 1, 3)
      tabs[[length(tabs) + 1]] <- tabPanel(short, DTOutput(paste0("tbl_", short)))
    }
    
    nf <- try(required_no_flights(), silent = TRUE)
    if (!inherits(nf, "try-error") && nrow(nf) > 0) {
      tabs[[length(tabs) + 1]] <- tabPanel("Required Routes with No Flights", DTOutput("tbl_missing"))
    }
    
    tabs[[length(tabs) + 1]] <- tabPanel("Routes Remaining", DTOutput("tbl_routes_remaining"))
    
    do.call(tabsetPanel, tabs)
  })
  
  # Day table outputs with DT perf options
  observe({
    req(input$plan, input$daily, input$merge)
    cal <- merged_calendar()$calendar
    if (!nrow(cal)) return(NULL)
    cal <- cal %>%
      mutate(
        Airline   = dplyr::coalesce(acr_air$name_map[`Airline Code`], `Airline Code`),
        DateLabel = date_label(dep_date),
        DepMin    = hhmm_to_min(`Departure Time`)
      ) %>%
      arrange(dep_date, DepMin, Airline, `Destination Code`)
    day_labels <- setNames(c("Sunday","Monday","Tuesday","Wednesday","Thursday","Friday","Saturday"),
                           c("Sun","Mon","Tue","Wed","Thu","Fri","Sat"))
    for (short in names(day_labels)) {
      local({
        s <- short
        full <- day_labels[[s]]
        out_id <- paste0("tbl_", s)
        df <- cal %>% filter(as.character(DayName) == full) %>%
          select(
            Date = DateLabel,
            Airline,
            `Destination`,
            `Departure Time`,
            `Assigned Surveys`,
            `Flight #`,
            Concourse,
            `Flight Type`,
            `Airline Code`,
            `Destination Code`,
            `Unique Route Number`
          )
        output[[out_id]] <- DT::renderDT({
          if (!nrow(df)) {
            DT::datatable(tibble(), options = list(dom = 't'))
          } else {
            DT::datatable(df, options = list(pageLength = 25, autoWidth = TRUE, deferRender = TRUE, scrollX = TRUE))
          }
        })
      })
    }
  })
  
  output$tbl_missing <- renderDT({
    nf <- required_no_flights()
    if (!nrow(nf)) {
      return(DT::datatable(tibble(Message = "All required routes have flights in the calendar."),
                           options = list(dom = 't')))
    }
    keep <- c("Airline","Destination","Assigned Surveys","Flight Type","Airline Code","Destination Code","Unique Route Number")
    DT::datatable(nf %>% select(all_of(keep)),
                  options = list(pageLength = 20, scrollX = TRUE, deferRender = TRUE))
  })
  
  output$tbl_routes_remaining <- renderDT({
    rr <- routes_remaining_all()
    if (!nrow(rr)) {
      return(DT::datatable(tibble(Message = "No routes found."), options = list(dom = 't')))
    }
    DT::datatable(rr, options = list(pageLength = 25, autoWidth = TRUE, deferRender = TRUE, scrollX = TRUE))
  })
  
  # ---------------------- Download calendar workbook ----------------------
  output$download_xlsx <- downloadHandler(
    filename = function() {
      req(input$daily, input$year_in)
      y  <- as.integer(input$year_in)
      mm <- month_from_daily()
      mon_abbr <- format(as.Date(sprintf("%04d-%02d-01", y, mm)), "%b")
      sprintf("Merged_Flight_And_Survey_Schedule_%04d_%s.xlsx", y, mon_abbr)
    },
    content = function(file) {
      routes  <- plan_routes()
      calendar <- merged_calendar()$calendar
      validate(need(nrow(calendar) > 0, "No calendar rows to write."))
      
      calendar <- calendar %>%
        mutate(
          DayNameFull = as.character(DayName),
          DateLabel   = date_label(dep_date),   # portable (no %-m/%-d on Windows)
          DepMin      = hhmm_to_min(`Departure Time`)
        ) %>%
        arrange(dep_date, DepMin, `Airline Code`, `Destination Code`)
      
      wb <- openxlsx::createWorkbook()
      
      # Parameters sheet
      openxlsx::addWorksheet(wb, "Parameters")
      params <- tibble(
        Parameter = c(
          "Export Timestamp", "Base %", "High % (≥4)", "High Rule Enabled", "Year", "Month",
          "Plan File", "Daily File", "Airline Acronyms", "Destination Acronyms"
        ),
        Value = c(
          format(Sys.time(), "%Y-%m-%d %H:%M:%S"),
          paste0(as.integer((as.numeric(input$pct_required) %||% 85)), "%"),
          if (isTRUE(input$hi_rule)) paste0(as.integer((as.numeric(input$pct_high) %||% 100)), "%") else "—",
          if (isTRUE(input$hi_rule)) "Yes" else "No",
          as.character(input$year_in),
          format(as.Date(sprintf("%04d-%02d-01", as.integer(input$year_in), month_from_daily())), "%B"),
          input$plan$name %||% "",
          input$daily$name %||% "",
          find_file(AIRLINES_FILE),
          find_file(DESTINATIONS_FILE)
        )
      )
      openxlsx::writeData(wb, "Parameters", params, keepNA = FALSE)
      openxlsx::freezePane(wb, "Parameters", firstRow = TRUE)
      openxlsx::setColWidths(wb, "Parameters", cols = 1:2, widths = c(28, 60))
      
      write_day_sheet <- function(day_name, short) {
        df <- calendar %>% dplyr::filter(DayNameFull == day_name)
        openxlsx::addWorksheet(wb, short)
        if (!nrow(df)) {
          openxlsx::writeData(wb, short,
                              data.frame(Message = sprintf("No flights for %s.", day_name)),
                              keepNA = FALSE)
          return(invisible())
        }
        out <- df %>%
          dplyr::select(
            Date               = dep_date,  # <-- write actual Date
            Airline,
            Destination        = `Destination`,
            `Departure Time`,
            `Assigned Surveys`,
            `Flight #`,
            Concourse,
            `Flight Type`,
            `Airline Code`,
            `Destination Code`,
            `Unique Route Number`
          )
        openxlsx::writeData(wb, short, out, keepNA = FALSE)
        openxlsx::addStyle(
          wb, short,
          style = openxlsx::createStyle(numFmt = "m/d"),
          rows = 2:(nrow(out) + 1), cols = 1, gridExpand = TRUE
        )
        openxlsx::freezePane(wb, short, firstRow = TRUE)
        openxlsx::setColWidths(wb, short, cols = 1:max(1, ncol(out)), widths = "auto")
      }
      
      # Sun..Sat order
      day_order <- list(
        "Sunday"    = "Sun",
        "Monday"    = "Mon",
        "Tuesday"   = "Tue",
        "Wednesday" = "Wed",
        "Thursday"  = "Thu",
        "Friday"    = "Fri",
        "Saturday"  = "Sat"
      )
      for (dn in names(day_order)) {
        write_day_sheet(dn, day_order[[dn]])
      }
      
      # Required Routes with No Flights
      nf <- required_no_flights()
      if (nrow(nf)) {
        openxlsx::addWorksheet(wb, "Required Routes with No Flights")
        out_nf <- nf %>%
          select(Airline, Destination, `Assigned Surveys`, `Flight Type`,
                 `Airline Code`, `Destination Code`, `Unique Route Number`)
        openxlsx::writeData(wb, "Required Routes with No Flights", out_nf, keepNA = FALSE)
        openxlsx::freezePane(wb, "Required Routes with No Flights", firstRow = TRUE)
        openxlsx::setColWidths(wb, "Required Routes with No Flights",
                               cols = 1:max(1, ncol(out_nf)), widths = "auto")
      }
      
      # Routes Remaining
      rr <- routes_remaining_all()
      if (nrow(rr)) {
        openxlsx::addWorksheet(wb, "Routes Remaining")
        openxlsx::writeData(wb, "Routes Remaining", rr, keepNA = FALSE)
        openxlsx::freezePane(wb, "Routes Remaining", firstRow = TRUE)
        openxlsx::setColWidths(wb, "Routes Remaining", cols = 1:max(1, ncol(rr)), widths = "auto")
      }
      
      # Missing Mappings (only if needed; plan-only)
      mmiss <- missing_mappings()
      if (nrow(mmiss)) {
        openxlsx::addWorksheet(wb, "Missing Mappings")
        openxlsx::writeData(wb, "Missing Mappings", mmiss, keepNA = FALSE)
        openxlsx::freezePane(wb, "Missing Mappings", firstRow = TRUE)
        openxlsx::setColWidths(wb, "Missing Mappings", cols = 1:max(1, ncol(mmiss)), widths = "auto")
      }
      
      openxlsx::saveWorkbook(wb, file, overwrite = TRUE)
    }
  )
}

shinyApp(ui, server)

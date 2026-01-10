# =========================================================
# Airport Survey Scheduler - (reads FormatASQFiles Mon..Sun + new sheets)
# =========================================================

# A hard coded maximum 40 surveys per day is encoded into this app.

# Interflight spacing rules are shown at the bottom of the app when month 3 is selected,
# but the rules are 10 minutes/2 surveys (10 minutes per survey, but there are two tablets to use)
# as well as 15 minutes for surveyors to change concourses between flights, if there is a concourse change.
suppressPackageStartupMessages({
  library(shiny)
  library(readxl)
  library(dplyr)
  library(tidyr)
  library(stringr)
  library(tibble)
  library(openxlsx)
  library(DT)
  library(lubridate)
})
options(shiny.fullstacktrace = TRUE)
# ---------------------- Constants & helpers ----------------------
DAY_LEVELS     <- c("Sun","Mon","Tue","Wed","Thu","Fri","Sat")
WEEKEND_DAYS   <- c("Sat","Sun")
HARD_COLOR     <- "#ffcdd2"
SOFT_COLOR     <- "#fff3cd"
`%||%` <- function(a,b) if (!is.null(a) && length(a)>0) a else b
is_weekend    <- function(day_name) day_name %in% WEEKEND_DAYS
nzint         <- function(x) {x <- suppressWarnings(as.integer(x)); ifelse(is.na(x),0L,x)}
comma         <- function(x) if (is.null(x) || length(x) == 0) "" else {
  v <- suppressWarnings(as.numeric(x)); v[!is.finite(v)] <- NA_real_
  out <- ifelse(is.na(v), "", formatC(v, digits = 0, format = "f", big.mark = ","))
  if (length(out) == 1) out[[1]] else paste(out, collapse = ", ")
}
as_plain_df <- function(x){
  if (is.null(x)) return(data.frame())
  if (!is.data.frame(x)) x <- as.data.frame(x, stringsAsFactors = FALSE)
  for (nm in names(x)) {
    col <- x[[nm]]
    if (is.list(col) && !is.data.frame(col)) {
      simple <- vapply(col, function(v) length(v) <= 1, logical(1))
      if (all(simple)) {
        x[[nm]] <- vapply(col, function(v) if (length(v)) as.character(v[[1]]) else "", character(1))
      } else {
        x[[nm]] <- vapply(col, function(v) paste(as.character(v), collapse = ", "), character(1))
      }
    } else if (!is.character(col)) {
      x[[nm]] <- as.character(col)
    }
  }
  class(x) <- setdiff(class(x), "tbl_df")
  x
}
fmt_md <- function(d) {
  if (inherits(d, "Date")) {
    lt <- as.POSIXlt(d)
    return(sprintf("%d-%d", lt$mon + 1L, lt$mday))
  }
  d2 <- suppressWarnings(as.Date(d))
  if (!is.na(d2)) {
    lt <- as.POSIXlt(d2)
    return(sprintf("%d-%d", lt$mon + 1L, lt$mday))
  }
  as.character(d)
}
# ---- time helpers ----
parse_user_time <- function(x) {
  if (is.null(x)) return(NA_integer_)
  if (inherits(x, c("POSIXct","POSIXlt"))) {
    lt <- as.POSIXlt(x, tz="UTC"); if (is.na(lt$hour)) return(NA_integer_); return(lt$hour*60 + lt$min)
  }
  if (is.numeric(x) && is.finite(x)) return(as.integer(round((x %% 1) * 1440)))
  s <- trimws(as.character(x)); if (!nzchar(s)) return(NA_integer_)
  if (grepl("(?i)\\b(am|pm)\\b", s, perl=TRUE)) {
    t1 <- try(as.POSIXlt(s, format="%I:%M %p", tz="UTC"), silent=TRUE)
    if (!inherits(t1,"try-error") && !is.na(t1$hour)) return(as.integer(t1$hour*60 + t1$min))
  }
  t2 <- try(as.POSIXlt(s, format="%H:%M", tz="UTC"), silent=TRUE)
  if (!inherits(t2,"try-error") && !is.na(t2$hour)) return(as.integer(t2$hour*60 + t2$min))
  m <- regexpr("(\\d{1,2}):(\\d{2})", s, perl=TRUE)
  if (m > 0) {
    frag <- substr(s, m, m + attr(m,"match.length")-1)
    hh <- suppressWarnings(as.integer(sub(":.*","",frag)))
    mm <- suppressWarnings(as.integer(sub(".*:","",frag)))
    if (!is.na(hh) && !is.na(mm)) return(as.integer(hh*60 + mm))
  }
  NA_integer_
}
mins_to_ampm <- function(m){
  if (!is.finite(m)) return("—")
  m <- as.integer(((m %% 1440)+1440)%%1440)
  hh <- m %/% 60; mm <- m %% 60; suf <- if (hh < 12) "AM" else "PM"
  hh12 <- hh %% 12; if (hh12 == 0) hh12 <- 12
  sprintf("%d:%02d %s", hh12, mm, suf)
}
to_ampm <- function(x) { v <- parse_user_time(x); if (!is.finite(v)) as.character(x) else mins_to_ampm(v) }
# ---- spacing (10 minutes per 2 surveys; +15 if concourse changes)
spacing_after <- function(S, concourse_change) {
  base <- 10L * ceiling((S %||% 0L)/2)
  if (isTRUE(concourse_change)) base <- base + 15L
  base
}
# Upper/trim a concourse value to a simple letter like "A", "B", "C"
cclean <- function(x) toupper(trimws(as.character(x)))
# ---- helpers for day/bin classification & summary ----
classify_bins <- function(df, earliest_cap_min = NULL, latest_cap_min = NULL) {
  if (is.null(df) || !nrow(df)) {
    return(list(
      wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L,
      pre6_flights=0L, after_cap_flights=0L,
      per_day = tibble(Day=character(0), AM=integer(0), PM=integer(0), Total=integer(0))
    ))
  }
  df <- tibble::as_tibble(df)
  if (!("Assigned Surveys" %in% names(df))) df[["Assigned Surveys"]] <- integer(nrow(df))
  if (!("Day" %in% names(df)))               df[["Day"]] <- rep(NA_character_, nrow(df))
  dep <- if ("DepMin" %in% names(df)) suppressWarnings(as.integer(df$DepMin)) else NA_integer_
  bad <- is.na(dep) | !is.finite(dep) | dep < 0 | dep > 1439
  if (any(bad) && "Departure Time" %in% names(df)) dep[bad] <- vapply(df$`Departure Time`, parse_user_time, integer(1))
  dep <- ((dep %% 1440) + 1440) %% 1440
  am_win <- is.finite(dep) & dep < 12*60
  pm_win <- is.finite(dep) & dep >= 12*60
  is_we <- df$Day %in% WEEKEND_DAYS
  is_wd <- !is_we
  wd_am <- sum(df[["Assigned Surveys"]][am_win & is_wd], na.rm = TRUE)
  wd_pm <- sum(df[["Assigned Surveys"]][pm_win & is_wd], na.rm = TRUE)
  we_am <- sum(df[["Assigned Surveys"]][am_win & is_we], na.rm = TRUE)
  we_pm <- sum(df[["Assigned Surveys"]][pm_win & is_we], na.rm = TRUE)
  { em <- if (!is.null(earliest_cap_min) && is.finite(earliest_cap_min)) as.integer(earliest_cap_min) else 6L*60L; pre6_flights <- sum(is.finite(dep) & dep < em & nzint(df[["Assigned Surveys"]]) > 0, na.rm = TRUE) }
  after_cap_flights <- if (!is.null(latest_cap_min) && is.finite(latest_cap_min)) {
    sum(is.finite(dep) & dep > latest_cap_min & nzint(df[["Assigned Surveys"]]) > 0, na.rm = TRUE)
  } else 0L
  per_day <- df %>%
    mutate(AM = ifelse(am_win, .data[["Assigned Surveys"]], 0L),
           PM = ifelse(pm_win, .data[["Assigned Surveys"]], 0L)) %>%
    group_by(.data$Day) %>%
    summarise(AM = sum(.data$AM, na.rm=TRUE), PM = sum(.data$PM, na.rm=TRUE),
              Total = sum(.data[["Assigned Surveys"]], na.rm=TRUE), .groups="drop") %>%
    arrange(factor(.data$Day, levels = DAY_LEVELS))
  list(
    wd_am = as.integer(wd_am), wd_pm = as.integer(wd_pm),
    we_am = as.integer(we_am), we_pm = as.integer(we_pm),
    pre6_flights = as.integer(pre6_flights),
    after_cap_flights = as.integer(after_cap_flights),
    per_day = per_day
  )
}
# ---------- Column mapping ----------
.colkey <- function(x) { x <- trimws(as.character(x)); x <- gsub("\\s+"," ",x); x <- gsub("[^A-Za-z0-9#]+","",x); tolower(x) }
alias_map <- c(
  airline="Airline", concourse="Concourse", origin="Origin", destination="Destination",
  "flight#"="Flight #", flightno="Flight #", flightnum="Flight #", flightnumber="Flight #",
  departuretime="Departure Time", daysofoperation="Days of Operation",
  sun="Sun", mon="Mon", tue="Tue", wed="Wed", thu="Thu", fri="Fri", sat="Sat",
  flighttype="Flight Type", uniqueroutenumber="Unique Route Number", routenumber="Unique Route Number", urn="Unique Route Number",
  assignedsurveys="Assigned Surveys", assigned="Assigned Surveys", remaining="Assigned Surveys",
  airlinecode="Airline Code", destinationcode="Destination Code"
)
map_to_canonical <- function(df) {
  if (is.null(df) || !ncol(df)) return(df)
  old  <- names(df)
  keys <- .colkey(old)
  for (i in seq_along(keys)) {
    k <- keys[i]
    target <- if (k %in% names(alias_map)) alias_map[[k]] else old[i]
    # reject NA / "" just in case
    if (is.na(target) || (is.character(target) && !nzchar(target))) target <- old[i]
    names(df)[i] <- target
  }
  names(df) <- vctrs::vec_as_names(names(df), repair = "unique")
  df
}
# ---------------------- Input readers (robust) ----------------------
read_weekday_sheets <- function(path){
  
  # Detect a date-like column by values, even if header is missing/odd
  detect_date_column <- function(df, sheet_name, y_guess){
    nm <- names(df)
    
    looks_like_date_vector <- function(v){
      # already Date?
      if (inherits(v, "Date")) return(TRUE)
      # NEW: handle POSIXt (readxl can return POSIXct for Excel date cells)
      if (inherits(v, c("POSIXct","POSIXlt"))) return(TRUE)
      
      # Excel serial (numeric) — broad but safe range (roughly 1980..2100)
      if (is.numeric(v)) {
        valid <- v[is.finite(v)]
        if (length(valid)) {
          rng <- range(valid, na.rm = TRUE)
          if (is.finite(rng[1]) && is.finite(rng[2]) && rng[1] >= 20000 && rng[2] <= 80000) return(TRUE)
        }
      }
      
      # character like m/d or m/d/yyyy
      if (is.character(v)) {
        s <- trimws(v)
        pat <- "^\\d{1,2}/\\d{1,2}(/\\d{2,4})?$"
        # treat as date if at least half of the non-blank values match
        nonblank <- s[nzchar(s)]
        if (!length(nonblank)) return(FALSE)
        hit <- sum(grepl(pat, nonblank))
        if (hit >= max(3, ceiling(0.5 * length(nonblank)))) return(TRUE)
      }
      
      FALSE
    }
    
    idx <- which(vapply(df, looks_like_date_vector, logical(1)))
    if (!length(idx)) {
      hdrs <- paste(ifelse(is.na(nm) | nm=="", "NA", nm), collapse = ", ")
      stop(paste0(
        "Sheet '", sheet_name, "' has no detectable Date column. ",
        "Expected date-like values (m/d or m/d/yyyy, Excel serial, or Date/POSIXt class). ",
        "Columns seen: {", hdrs, "}."
      ))
    }
    
    col <- idx[1]
    
    # Build dep_date from selected column
    v <- df[[col]]
    if (inherits(v, "Date")) {
      dep_date <- v
    } else if (inherits(v, c("POSIXct","POSIXlt"))) {
      # NEW: coerce POSIXct/POSIXlt to Date
      dep_date <- as.Date(v)
    } else if (is.numeric(v)) {
      # readxl uses 1899-12-30 origin for Excel serials
      dep_date <- as.Date(v, origin = "1899-12-30")
    } else {
      s <- trimws(as.character(v))
      pat_md  <- "^\\d{1,2}/\\d{1,2}$"
      pat_mdy <- "^\\d{1,2}/\\d{1,2}/\\d{2,4}$"
      dep_date <- suppressWarnings({
        if (all(grepl(pat_md, s) | s == "" | is.na(s))) {
          mm <- as.integer(sub("^([0-9]{1,2})/.*$", "\\1", s))
          dd <- as.integer(sub("^[0-9]{1,2}/([0-9]{1,2}).*$", "\\1", s))
          as.Date(sprintf("%04d-%02d-%02d", y_guess, mm, dd))
        } else if (all(grepl(pat_mdy, s) | s == "" | is.na(s))) {
          lubridate::mdy(s)
        } else {
          # mixed but still try lubridate
          lubridate::mdy(s)
        }
      })
      if (any(is.na(dep_date) & nzchar(s))) {
        stop(paste0("Sheet '", sheet_name, "': could not parse some Date values."))
      }
    }
    
    list(dep_date = dep_date, date_col_index = col)
  }
  
  shs <- try(readxl::excel_sheets(path), silent = TRUE)
  if (inherits(shs, "try-error") || length(shs) == 0) stop("Cannot read workbook.")
  
  ok_short <- intersect(DAY_LEVELS, shs)
  ok_long  <- intersect(c("Sunday","Monday","Tuesday","Wednesday","Thursday","Friday","Saturday"), shs)
  if ((length(ok_short) + length(ok_long)) == 0) stop("No weekday sheets found (Sun..Sat).")
  
  # Year hint from filename, fall back to current
  y_guess <- suppressWarnings(as.integer(stringr::str_extract(basename(path), "(?<!\\d)(20\\d{2})(?!\\d)")))
  if (is.na(y_guess)) y_guess <- as.integer(format(Sys.Date(), "%Y"))
  
  read_one <- function(sh, day_short){
    df_raw <- suppressMessages(readxl::read_excel(path, sheet = sh))
    names(df_raw) <- trimws(names(df_raw))
    
    # Detect & build dep_date BEFORE any column remapping
    dd <- detect_date_column(df_raw, sh, y_guess)
    dep_date <- dd$dep_date
    
    # Now map other columns to canonical names (does NOT drop extra columns)
    df <- map_to_canonical(df_raw)
    
    if ("Concourse" %in% names(df)) df$Concourse <- toupper(trimws(as.character(df$Concourse)))
    
    # Require only the fields we truly need (Date header not required anymore)
    req_cols <- c("Airline","Destination","Departure Time","Flight #","Concourse",
                  "Unique Route Number","Flight Type","Airline Code","Destination Code")
    missing <- setdiff(req_cols, names(df))
    if (length(missing) > 0) {
      stop(paste0("Sheet '", sh, "' is missing: ", paste(missing, collapse = ", ")))
    }
    
    # Attach dep_date, parse DepMin, add Day
    df$dep_date <- as.Date(dep_date)
    df$DepMin   <- vapply(df$`Departure Time`, parse_user_time, integer(1))
    df$DepMin   <- ((df$DepMin %% 1440) + 1440) %% 1440
    df$Day      <- day_short
    
    df
  }
  
  out <- list()
  for (d in DAY_LEVELS) if (d %in% shs) out[[length(out) + 1]] <- read_one(d, d)
  long_map <- c(Sunday="Sun", Monday="Mon", Tuesday="Tue", Wednesday="Wed",
                Thursday="Thu", Friday="Fri", Saturday="Sat")
  for (nm in names(long_map)) if (nm %in% shs) out[[length(out) + 1]] <- read_one(nm, long_map[[nm]])
  
  dplyr::bind_rows(out)
}
read_routes_remaining <- function(path){
  sheets <- readxl::excel_sheets(path)
  
  # Fallback: if workbook has no "Routes Remaining" sheet, return a 0-row table
  # with the expected columns so downstream code keeps working.
  if (!"Routes Remaining" %in% sheets) {
    return(data.frame(
      Airline              = character(0),
      Destination          = character(0),
      `Assigned Surveys`   = integer(0),
      `Flight Type`        = character(0),
      `Airline Code`       = character(0),
      `Destination Code`   = character(0),
      `Unique Route Number`= integer(0),
      `Days of Operation`  = character(0),
      check.names = FALSE,
      stringsAsFactors = FALSE
    ))
  }
  
  rr <- suppressMessages(readxl::read_excel(path, sheet = "Routes Remaining"))
  rr <- map_to_canonical(rr); names(rr) <- trimws(names(rr))
  
  need <- c("Airline","Destination","Assigned Surveys","Flight Type",
            "Airline Code","Destination Code","Unique Route Number","Days of Operation")
  missing <- setdiff(need, names(rr))
  if (length(missing)) stop(paste("Routes Remaining missing:", paste(missing, collapse=", ")))
  
  rr$`Unique Route Number` <- nzint(rr$`Unique Route Number`)
  rr$`Assigned Surveys`    <- nzint(rr$`Assigned Surveys`)
  rr
}

read_required_no_flights <- function(path){
  sheets <- readxl::excel_sheets(path)
  if (!"Required Routes with No Flights" %in% sheets) return(NULL)
  nf <- suppressMessages(readxl::read_excel(path, sheet = "Required Routes with No Flights"))
  nf <- map_to_canonical(nf); names(nf) <- trimws(names(nf))
  keep <- c("Airline","Destination","Assigned Surveys","Flight Type",
            "Airline Code","Destination Code","Unique Route Number")
  missing <- setdiff(keep, names(nf))
  if (length(missing)) stop(paste("'Required Routes with No Flights' is missing:", paste(missing, collapse=", ")))
  nf$`Unique Route Number` <- nzint(nf$`Unique Route Number`)
  nf$`Assigned Surveys`    <- nzint(nf$`Assigned Surveys`)
  nf
}
# ---------------------- UI ----------------------
ui <- fluidPage(
  titlePanel("Airport Survey Schedule Maker"),
  div(id = "busy-overlay", div(id = "busy-box", "Generating…")),
  tags$head(
    tags$style(HTML("
      #busy-overlay{position:fixed;inset:0;display:none;align-items:center;justify-content:center;background:rgba(255,255,255,.82);z-index:9999;}
      .shiny-busy #busy-overlay{display:flex;}
      #busy-box{background:#f7f7f7;border:1px solid #ddd;padding:16px 22px;border-radius:10px;font-weight:600;box-shadow:0 6px 20px rgba(0,0,0,.12);}
    "))
  ),
  sidebarLayout(
    sidebarPanel(width=4,
                 uiOutput("surveys_header"),
                 fluidRow(
                   column(6, strong("Available To Be Assigned:"), br(), textOutput("possible_sched", inline = TRUE)),
                   column(6, strong("Route(s) Not Listed in Flight Schedule:"), br(), textOutput("impossible_period", inline = TRUE))
                 ),
                 tags$hr(),
                 fileInput("file", "Upload Merged Output Excel (xlsx from App #1)", accept = c(".xlsx")),
                 selectInput("month_index", "Month of Quarter", choices = c("Month 1 or 2"=1, "Month 3"=3), selected = 1),
                 tags$hr(),
                 h4("Select Up To Four Days"),
                 selectizeInput(
                   "day1","Day 1",
                   choices = c("None", DAY_LEVELS), selected = "None", width = "100%",
                   options = list(
                     onDropdownOpen = I('function($dropdown){
                      var c = $dropdown.find(".selectize-dropdown-content");
                      if (c && c.length) {
                        c.css("max-height","none");
                        c.css("overflow-y","visible");
                      }
                    }')
                   )
                 ),
                 selectizeInput(
                   "day2","Day 2",
                   choices = c("None", DAY_LEVELS), selected = "None", width = "100%",
                   options = list(
                     onDropdownOpen = I('function($dropdown){
                      var c = $dropdown.find(".selectize-dropdown-content");
                      if (c && c.length) {
                        c.css("max-height","none");
                        c.css("overflow-y","visible");
                      }
                    }')
                   )
                 ),
                 selectizeInput(
                   "day3","Day 3",
                   choices = c("None", DAY_LEVELS), selected = "None", width = "100%",
                   options = list(
                     onDropdownOpen = I('function($dropdown){
                      var c = $dropdown.find(".selectize-dropdown-content");
                      if (c && c.length) {
                        c.css("max-height","none");
                        c.css("overflow-y","visible");
                      }
                    }')
                   )
                 ),
                 selectizeInput(
                   "day4","Day 4",
                   choices = c("None", DAY_LEVELS), selected = "None", width = "100%",
                   options = list(
                     onDropdownOpen = I('function($dropdown){
                      var c = $dropdown.find(".selectize-dropdown-content");
                      if (c && c.length) {
                        c.css("max-height","none");
                        c.css("overflow-y","visible");
                      }
                    }')
                   )
                 ),
                 tags$hr(),
                 checkboxInput("restrict_dates_master", "Specify which dates can be chosen", value = FALSE),
                 uiOutput("dateFiltersUI"),
                 checkboxInput("fine_tune_days", "Fine tune max hours and surveys per selected day", value = FALSE),
                 uiOutput("fineTuneUI"),
                 tags$hr(),
                 uiOutput("targetsUI"),
                 uiOutput("amControlsUI"),
                 tags$hr(),
                 checkboxInput("hard_earliest", "Hard Limit for Earliest Departure Time?", value = TRUE),
                 conditionalPanel(
                   "input.hard_earliest",
                   textInput("earliest_dep","Earliest Departure Time for Schedules", value = "6:00 AM")
                 ),
                 checkboxInput("hard_latest", "Hard Limit for Latest Departure Time?", value = TRUE),
                 conditionalPanel(
                   "input.hard_latest",
                   textInput("latest_dep","Latest Departure Time for Schedules", value = "8:45 PM")
                 ),
                 tags$hr(),
                 conditionalPanel(
                   "Number(input.month_index) === 3",
                   checkboxInput("m3_hard_hours", "Enforce Maximum Daily Hours?", value = FALSE)
                 ),
                 conditionalPanel(
                   "!input.fine_tune_days && (Number(input.month_index) === 1 || (Number(input.month_index) === 3 && input.m3_hard_hours))",
                   numericInput("max_hours","Maximum Daily Hours", value = 6, min = 1, max = 24, step = 1)
                 ),
                 tags$hr(),
                 numericInput("per_flight_cap","Maximum surveys per flight", value = 10, min = 1, step = 1),
                 tags$hr(),
                 checkboxInput("prior_intl",   "Prioritize International Routes", value = TRUE),
                 checkboxInput("prior_infreq", "Prioritize Infrequent Routes",    value = TRUE),
                 tags$hr(),
                 conditionalPanel(
                   "Number(input.month_index) === 3",
                   tagList(
                     checkboxInput("enforce_spacing", "Enforce Interflight Spacing Rules?", value = FALSE),
                     helpText(tags$small("10 minutes/2 surveys and 15 minute buffer for concourse changes"))
                   )
                 ),
                 tags$hr(),
                 actionButton("generate","Generate Schedule", class="btn-primary"),
                 downloadButton("download","Download Workbook")
    ),
    mainPanel(width=8, uiOutput("mainTabsUI"))
  ),
)
# ---------------------- Server ----------------------
server <- function(input, output, session){
  room_ampm2 <- 1000000000L
  # ---- Safe debug options (Shiny calls shiny.error with 0 args) ----
  local({
    # Show warnings but do NOT turn them into errors while we debug
    options(warn = 1)
    
    # Shiny invokes this with no arguments; use geterrmessage()/traceback()
    options(shiny.error = function(){
      msg <- geterrmessage()
      cat("\n--- Shiny error ---\n", msg, "\n", sep = "")
      # best-effort stack trace (2 = skip this handler frame)
      try(traceback(2), silent = TRUE)
    })
  })
  # Speed: enable byte-code compilation/JIT if available
  if (requireNamespace("compiler", quietly = TRUE)) compiler::enableJIT(3)
  
  # -------- read everything --------
  flights_df <- reactive({
    req(input$file)
    tryCatch({
      df <- read_weekday_sheets(input$file$datapath)
      validate(need(nrow(df) > 0, "No rows read from weekday sheets."))
      df
    }, error = function(e) {
      showNotification(paste("Read failed:", conditionMessage(e)), type = "error", duration = 10)
      stop(e)
    })
  })
  
  routes_remaining <- reactive({
    req(input$file)
    read_routes_remaining(input$file$datapath)
  })
  req_no_flights <- reactive({
    req(input$file)
    read_required_no_flights(input$file$datapath)
  })
  
  # -------- header counters --------
  totals <- reactive({
    if (!isTruthy(input$file)) return(list(schedulable=NA_integer_, impossible=NA_integer_, total_all=NA_integer_))
    rr <- routes_remaining()
    nf <- req_no_flights()
    total_all <- sum(nzint(rr$`Assigned Surveys`), na.rm = TRUE)
    impossible <- if (is.null(nf)) 0L else sum(nzint(nf$`Assigned Surveys`), na.rm = TRUE)
    schedulable <- total_all - impossible
    list(schedulable = as.integer(schedulable), impossible = as.integer(impossible), total_all = as.integer(total_all))
  })
  
  output$surveys_header <- renderUI({
    val <- ""
    if (isTruthy(input$file)) {
      t <- totals()
      if (!is.null(t) && !is.na(t$total_all)) val <- comma(t$total_all)
    }
    tags$h4(tagList("Surveys Remaining:", if (nzchar(val)) span(" ", strong(val)) else NULL))
  })
  output$possible_sched <- renderText({ if (!isTruthy(input$file)) return(""); t <- totals(); comma(t$schedulable) })
  output$impossible_period <- renderText({ if (!isTruthy(input$file)) return(""); t <- totals(); comma(t$impossible) })
  
  # -------- selected days and date filters --------
  selected_days <- reactive({
    days <- c(input$day1,input$day2,input$day3,input$day4)
    days[days %in% DAY_LEVELS]
  })
  output$dateFiltersUI <- renderUI({
    req(input$restrict_dates_master)
    df <- flights_df()
    if (is.null(df) || !nrow(df)) return(NULL)
    # Map Day 1–4 selectors into the slots actually in use
    slot_labels <- c(input$day1, input$day2, input$day3, input$day4)
    slot_idx    <- which(slot_labels %in% DAY_LEVELS)
    if (!length(slot_idx)) {
      return(helpText("Select days above."))
    }
    make_for_slot <- function(slot_no, day_label) {
      dates <- df %>%
        dplyr::filter(Day == day_label) %>%
        dplyr::pull(dep_date) %>%
        unique() %>%
        sort()
      if (!length(dates)) return(NULL)
      values <- as.character(dates)
      labels <- vapply(dates, fmt_md, character(1))
      choices <- setNames(values, labels)
      input_id <- paste0("dates_slot", slot_no)
      # Preserve existing selection for this slot if possible
      old <- isolate(input[[input_id]])
      if (!is.null(old) && length(old)) {
        keep <- intersect(old, values)
        if (length(keep)) values <- keep
      }
      wellPanel(
        h5(paste0("Day ", slot_no, " — ", day_label)),
        checkboxGroupInput(
          inputId = input_id,
          label   = "Allowed dates:",
          choices = choices,
          selected = values
        )
      )
    }
    panels <- lapply(slot_idx, function(idx) make_for_slot(idx, slot_labels[idx]))
    do.call(tagList, panels)
  })
  # -------- Fine tune UI --------
  output$fineTuneUI <- renderUI({
    if (!isTRUE(input$fine_tune_days)) return(NULL)
    days <- selected_days(); if (!length(days)) return(helpText("Select days first."))
    is_m3 <- as.integer(input$month_index) == 3
    tagList(
      lapply(seq_along(days), function(i){
        wellPanel(
          h5(days[i]),
          fluidRow(
            column(6, numericInput(paste0("ft_hours_", i), paste0(days[i], " — Max Hours (blank=no max)"), value = NA, min=1, max=24, step=1)),
            column(6, numericInput(paste0("ft_surveys_", i), paste0(days[i], " — Max Surveys (blank=40)"), value = NA, min=0, step=1))
          )
        )
      })
    )
  })
  
  # -------- Month targets / bin caps UI --------
  output$targetsUI <- renderUI({
    month <- as.integer(input$month_index)
    days  <- selected_days()
    wk_present <- any(days %in% WEEKEND_DAYS)
    if (month %in% c(1,2)) {
      NULL
    } else {
      div(
        h4("Desired distribution (Month 3) — Bin caps"),
        helpText("Maximum desired assigned surveys by bin"),
        fluidRow(
          column(6, numericInput("m3_wd_am","Weekday AM (max desired)", value = 0, min=0, step=1)),
          column(6, numericInput("m3_wd_pm","Weekday PM (max desired)", value = 0, min=0, step=1))
        ),
        if (wk_present) fluidRow(
          column(6, numericInput("m3_we_am","Weekend AM (max desired)", value = 0, min=0, step=1)),
          column(6, numericInput("m3_we_pm","Weekend PM (max desired)", value = 0, min=0, step=1))
        )
      )
    }
  })
  
  # --- Auto-populate Month 3 desired distribution (percent-based defaults)
  # ---- Auto-populate Month 3 desired distribution (caps) ----
  prev_days_m3 <- reactiveVal(NULL)
  observeEvent(list(input$month_index, selected_days(), totals()), {
    if (as.integer(input$month_index) != 3L) return()
    days <- selected_days()
    if (!length(days)) {
      prev_days_m3(NULL)
      return()
    }
    # Decide whether to auto-fill or keep any user-entered caps.
    old_days <- prev_days_m3()
    skip_autofill <- FALSE
    if (!is.null(old_days) && length(old_days) && length(days) &&
        length(old_days) == length(days)) {
      old_is_we <- vapply(old_days, is_weekend, logical(1))
      new_is_we <- vapply(days,     is_weekend, logical(1))
      if (identical(old_is_we, new_is_we)) {
        # Same number of slots and the same weekday/weekend pattern:
        # user is just rotating weekdays (e.g. Mon -> Tue), so keep their caps.
        skip_autofill <- TRUE
      }
    }
    if (skip_autofill) {
      # Update stored pattern and leave existing numericInputs alone.
      prev_days_m3(days)
      return()
    }
    total <- as.integer(totals()$schedulable %||% 0L)
    if (!is.finite(total) || total <= 0L) {
      prev_days_m3(days)
      return()
    }
    # Percentages you specified
    wd_am_p <- 0.2925
    wd_pm_p <- 0.3475
    we_am_p <- 0.1575
    we_pm_p <- 0.1925
    wk_present <- any(days %in% WEEKEND_DAYS)
    if (wk_present) {
      wd_am <- round(total * wd_am_p)
      wd_pm <- round(total * wd_pm_p)
      we_am <- round(total * we_am_p)
      # Make sure the four buckets sum to total, put remainder into WE PM
      we_pm <- as.integer(total - wd_am - wd_pm - we_am)
    } else {
      # No weekend days selected: normalize WD AM/PM to 100% of total
      wd_sum <- wd_am_p + wd_pm_p
      wd_am  <- round(total * (wd_am_p / wd_sum))
      wd_pm  <- as.integer(total - wd_am)
      we_am  <- 0L
      we_pm  <- 0L
    }
    updateNumericInput(session, "m3_wd_am", value = wd_am)
    updateNumericInput(session, "m3_wd_pm", value = wd_pm)
    if (wk_present) {
      updateNumericInput(session, "m3_we_am", value = we_am)
      updateNumericInput(session, "m3_we_pm", value = we_pm)
    } else {
      if (!is.null(input$m3_we_am)) updateNumericInput(session, "m3_we_am", value = 0L)
      if (!is.null(input$m3_we_pm)) updateNumericInput(session, "m3_we_pm", value = 0L)
    }
    prev_days_m3(days)
  }, ignoreInit = FALSE)
  
  # -------- AM controls (Month 1/2 only) --------
  output$amControlsUI <- renderUI({
    month <- as.integer(input$month_index)
    if (!(month %in% c(1, 2))) return(NULL)
    days <- selected_days()
    wk_present <- any(days %in% WEEKEND_DAYS)
    if (!wk_present) {
      # Ensure split is OFF when no weekend day is selected
      isolate({
        if (isTRUE(input$split_week_wknd)) {
          updateCheckboxInput(session, "split_week_wknd", value = FALSE)
        }
      })
      return(tagList(
        sliderInput("am_pct", "AM % (rest PM %)",
                    min = 0, max = 100, value = isolate(input$am_pct %||% 45), step = 1)
      ))
    }
    
    # Weekend present: show the checkbox and conditional UI
    tagList(
      checkboxInput("split_week_wknd",
                    "Specify AM/PM split separately for Weekday & Weekend",
                    value = isTRUE(input$split_week_wknd)),
      conditionalPanel(
        "input.split_week_wknd == false",
        sliderInput("am_pct", "AM % (rest PM %)",
                    min = 0, max = 100, value = isolate(input$am_pct %||% 45), step = 1)
      ),
      conditionalPanel(
        "input.split_week_wknd == true",
        fluidRow(
          column(12, strong("Weekday AM %")),
          column(12, sliderInput("am_pct_wd", "", min = 0, max = 100,
                                 value = isolate(input$am_pct_wd %||% 45), step = 1))
        ),
        fluidRow(
          column(12, strong("Weekend AM %")),
          column(12, sliderInput("am_pct_we", "", min = 0, max = 100,
                                 value = isolate(input$am_pct_we %||% 45), step = 1))
        )
      )
    )
  })
  
  # Safety: if user deselects all weekend days, force split off
  observeEvent(selected_days(), {
    if (!any(selected_days() %in% WEEKEND_DAYS) && isTRUE(input$split_week_wknd)) {
      updateCheckboxInput(session, "split_week_wknd", value = FALSE)
    }
  }, ignoreInit = TRUE)
  # Default behavior by Month: OFF in Month 3, ON in Months 1/2 (both earliest & latest)
  observeEvent(input$month_index, {
    idx <- as.integer(input$month_index %||% 1L)
    updateCheckboxInput(session, "hard_latest",   value = !(idx == 3L))
    updateCheckboxInput(session, "hard_earliest", value = !(idx == 3L))
  }, ignoreInit = TRUE)
  # Track if the user has manually toggled interflight spacing
  spacing_touched <- reactiveVal(FALSE)
  observeEvent(input$enforce_spacing, { spacing_touched(TRUE) }, ignoreInit = TRUE)
  
  # Default checkbox value (only when Month 3) unless user already touched it
  observeEvent(input$month_index, {
    idx <- as.integer(input$month_index %||% 1L)
    if (idx == 3L && !isTRUE(spacing_touched())) {
      updateCheckboxInput(session, "enforce_spacing", value = FALSE)
    }
  }, ignoreInit = TRUE)
  
  # -------- state --------
  state <- reactiveValues(
    day_list = NULL, schedules = NULL, assigned_long = NULL,
    routes_updated = NULL, nf_tbl = NULL, summary = NULL,
    bypassed = NULL, unscheduled_reasons = NULL,
    latest_cap_min = NULL, date_fit = NULL, has_run_generate = FALSE,
    debug = list(), debug_rows = 0L,
    debug_urn = NA_integer_
  )
  observe({
    state$debug_urn <- as.integer(input$debug_urn %||% NA_integer_)
  })
  # ---- helpers ----
  # --- Global helpers used by window scoring & early paths ---
  global_am_pm_counts <- function() {
    # Prefer an in-scope 'assignments' list if present; otherwise fall back to
    # the flat table we render (state$assigned_long).
    am <- 0L; tot <- 0L; am_wd <- 0L; tot_wd <- 0L; am_we <- 0L; tot_we <- 0L
    
    asg <- get0("assignments", inherits = TRUE, ifnotfound = NULL)
    if (is.list(asg) && length(asg)) {
      for (nm in names(asg)) {
        df_asg <- asg[[nm]]
        if (is.data.frame(df_asg) && nrow(df_asg)) {
          k <- as.integer(sum(as.integer(df_asg$`Assigned Surveys` %||% 0L), na.rm = TRUE))
          if (is.finite(k) && k > 0L) {
            mins <- if ("DepMin" %in% names(df_asg)) {
              as.integer(df_asg$DepMin)
            } else {
              vapply(df_asg$`Departure Time`, parse_user_time, integer(1))
            }
            is_am_asg <- is.finite(mins) & (mins < 12*60)
            amc <- as.integer(sum(as.integer(df_asg$`Assigned Surveys`[is_am_asg] %||% 0L), na.rm = TRUE))
            tot <- tot + k; am <- am + amc
            if (is_weekend(nm)) {
              tot_we <- tot_we + k; am_we <- am_we + amc
            } else {
              tot_wd <- tot_wd + k; am_wd <- am_wd + amc
            }
          }
        }
      }
      return(list(am = am, tot = tot, am_wd = am_wd, tot_wd = tot_wd, am_we = am_we, tot_we = tot_we))
    }
    
    df <- state$assigned_long
    if (is.data.frame(df) && nrow(df)) {
      mins <- if ("DepMin" %in% names(df)) {
        as.integer(df$DepMin)
      } else {
        vapply(as.character(df$`Departure Time`), parse_user_time, integer(1))
      }
      is_am <- is.finite(mins) & (mins < 12*60)
      am  <- as.integer(sum(as.integer(df$`Assigned Surveys`[is_am] %||% 0L), na.rm = TRUE))
      tot <- as.integer(sum(as.integer(df$`Assigned Surveys` %||% 0L), na.rm = TRUE))
      
      if ("Day" %in% names(df)) {
        wd_mask <- !(as.character(df$Day) %in% WEEKEND_DAYS)
      } else {
        wd_mask <- rep(TRUE, nrow(df))
      }
      am_wd <- as.integer(sum(as.integer(df$`Assigned Surveys`[is_am & wd_mask] %||% 0L), na.rm = TRUE))
      tot_wd <- as.integer(sum(as.integer(df$`Assigned Surveys`[wd_mask] %||% 0L), na.rm = TRUE))
      
      we_mask <- !wd_mask
      am_we <- as.integer(sum(as.integer(df$`Assigned Surveys`[is_am & we_mask] %||% 0L), na.rm = TRUE))
      tot_we <- as.integer(sum(as.integer(df$`Assigned Surveys`[we_mask] %||% 0L), na.rm = TRUE))
    }
    
    list(am = am, tot = tot, am_wd = am_wd, tot_wd = tot_wd, am_we = am_we, tot_we = tot_we)
  }
  
  get_targets <- function() {
    split <- isTRUE(input$split_week_wknd)
    if (!split) {
      am_g <- as.numeric(input$am_pct %||% 45)
      am_g <- max(0, min(100, am_g))
      list(split = FALSE, am_global = am_g)
    } else {
      am_wd <- as.numeric(input$am_pct_wd %||% 45)
      am_we <- as.numeric(input$am_pct_we %||% 45)
      list(split = TRUE,
           am_wd = max(0, min(100, am_wd)),
           am_we = max(0, min(100, am_we)))
    }
  }
  # ---- debug trace helpers ----
  debug_reset <- function() { state$debug <- list(); state$debug_rows <- 0L }
  debug_note <- function(day, slot, step, info = list()) {
    state$debug_rows <- as.integer(state$debug_rows %||% 0L) + 1L
    entry <- c(
      list(Day  = as.character(day %||% "")),
      list(Slot = as.integer(slot %||% NA_integer_)),
      list(Step = as.character(step %||% ""))
    )
    if (length(info)) entry <- c(entry, info)
    state$debug[[state$debug_rows]] <- entry
    invisible(NULL)
  }
  debug_trace_pool <- function(pool) {
    urn <- as.integer(state$debug_urn %||% NA_integer_)
    if (!is.finite(urn)) {
      return(list(
        trace_urn       = NA_integer_,
        trace_in_pool   = NA_integer_,
        trace_remaining = NA_integer_
      ))
    }
    if (!is.data.frame(pool) || !nrow(pool)) {
      return(list(
        trace_urn       = urn,
        trace_in_pool   = 0L,
        trace_remaining = NA_integer_
      ))
    }
    urn_col <- if ("Unique Route Number" %in% names(pool)) {
      suppressWarnings(as.integer(pool$`Unique Route Number`))
    } else if ("URN" %in% names(pool)) {
      suppressWarnings(as.integer(pool$URN))
    } else {
      rep(NA_integer_, nrow(pool))
    }
    in_pool <- any(is.finite(urn_col) & urn_col == urn, na.rm = TRUE)
    rem <- NA_integer_
    if (in_pool && "remaining" %in% names(pool)) {
      idx <- which(is.finite(urn_col) & urn_col == urn)[1]
      rem <- suppressWarnings(as.integer(pool$remaining[idx]))
    }
    list(
      trace_urn       = urn,
      trace_in_pool   = as.integer(if (isTRUE(in_pool)) 1L else 0L),
      trace_remaining = as.integer(rem)
    )
  }
  # Build a flat data frame from the debug trace list captured via debug_note()
  debug_table <- function() {
    dbg <- state$debug %||% list()
    n  <- length(dbg)
    if (!n) return(data.frame())
    
    rows <- lapply(seq_len(n), function(i) {
      e <- dbg[[i]]
      if (!is.list(e)) return(NULL)
      df <- as.data.frame(e, stringsAsFactors = FALSE)
      df$Seq <- i
      df
    })
    out <- suppressWarnings(dplyr::bind_rows(rows))
    
    # Put the most helpful columns first if present
    head_cols <- intersect(c("Seq","Day","Slot","Step","URN","DepMin2","DepMin"), names(out))
    other     <- setdiff(names(out), head_cols)
    out <- out[, c(head_cols, other), drop = FALSE]
    
    # Pretty departure time if DepMin captured in any notes
    if ("DepMin" %in% names(out)) {
      out$`Departure Time` <- vapply(out$DepMin, mins_to_ampm, character(1))
    }
    
    # Pretty window/limit times (minutes since midnight) if present
    safe_ampm <- function(x) {
      x <- suppressWarnings(as.integer(x))
      if (!is.finite(x) || x < 0L) return(NA_character_)
      mins_to_ampm(x)
    }
    
    pretty_min_cols <- intersect(
      c(
        "first_time","max_time","allow_min","allow_max",
        "earliest_cap","latest_cap",
        "earliest_start_allowed","latest_start_allowed"
      ),
      names(out)
    )
    for (nm in pretty_min_cols) {
      out[[paste0(nm, "_time")]] <- vapply(out[[nm]], safe_ampm, character(1))
    }
    
    if (all(c("allow_min_time","allow_max_time") %in% names(out))) {
      out$allow_window <- ifelse(
        !is.na(out$allow_min_time) & !is.na(out$allow_max_time),
        paste0("[", out$allow_min_time, "\u2013", out$allow_max_time, "]"),
        NA_character_
      )
    }
    
    out
  }
  join_oxford <- function(x){
    x <- as.character(x)
    if (length(x)==1) return(x)
    if (length(x)==2) return(paste(x, collapse=" and "))
    paste0(paste(x[-length(x)], collapse=", "), ", and ", x[length(x)])
  }
  
  # --- Helper used by schedule_one_day (OK to replace if you already have it) ---
  flight_bin <- function(day_chr, dep_min) {
    is_we <- day_chr %in% WEEKEND_DAYS
    is_am <- all(is.finite(dep_min)) && all(dep_min < 12*60)
    if (!is_we &&  is_am) return("wd_am")
    if (!is_we && !is_am) return("wd_pm")
    if ( is_we &&  is_am) return("we_am")
    if ( is_we && !is_am) return("we_pm")
    NA_character_
  }
  
  # -------- Pick best time window (e.g., 6 hours) to maximize assignable surveys --------
  best_time_window <- function(df_day, route_remaining, day_cap, hours_cap,
                               controls, month, bin_caps, already_assigned_bins, day_name){
    if (!nrow(df_day)) return(NULL)
    
    # Precompute minutes (reuse if present to avoid re-parsing)
    cand <- df_day
    if (!("DepMin" %in% names(cand))) {
      cand$DepMin <- vapply(cand$`Departure Time`, parse_user_time, integer(1))
    }
    cand$DepMin <- ((cand$DepMin %% 1440) + 1440) %% 1440
    cand <- cand[is.finite(cand$DepMin), , drop = FALSE]
    
    latest_cap   <- if (isTRUE(controls$hard_latest))   parse_user_time(controls$latest_dep)   else parse_user_time("11:59 PM")
    earliest_cap <- if (isTRUE(controls$hard_earliest)) parse_user_time(controls$earliest_dep) else parse_user_time("5:00 AM")
    
    if (isTRUE(controls$hard_latest) && is.finite(latest_cap)) {
      cand <- cand[cand$DepMin <= latest_cap, , drop = FALSE]
    }
    if (isTRUE(controls$hard_earliest) && is.finite(earliest_cap)) {
      cand <- cand[cand$DepMin >= earliest_cap, , drop = FALSE]
    }
    if (!nrow(cand)) return(NULL)
    
    # Remaining by URN and per-flight cap (faster than left_join)
    cand$remaining <- {
      ru  <- route_remaining
      idx <- match(cand$`Unique Route Number`, ru$`Unique Route Number`)
      out <- integer(nrow(cand)); out[] <- 0L
      has <- !is.na(idx)
      out[has] <- nzint(ru$remaining[idx[has]])
      out
    }
    per_f_cap <- as.integer(nzint(controls$per_flight_cap %||% 10L))
    
    # Bin room (Month 3)
    assigned_bins <- list(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)
    if (!is.null(already_assigned_bins)) {
      for (k in names(assigned_bins)) {
        if (!is.null(already_assigned_bins[[k]])) assigned_bins[[k]] <- as.integer(already_assigned_bins[[k]])
      }
    }
    bin_room_remaining <- function(bin_name) {
      if (is.null(bin_caps) || is.null(bin_caps[[bin_name]]) || !is.finite(as.numeric(bin_caps[[bin_name]]))) return(1e9L)
      cap <- as.integer(bin_caps[[bin_name]] %||% 0L)
      used <- as.integer(assigned_bins[[bin_name]] %||% 0L)
      pmax(0L, cap - used)
    }
    cand$bin <- mapply(flight_bin, cand$Day, cand$DepMin)
    # Precompute weekly frequency per URN from 'Days of Operation' (e.g., "1234567", "1..4..7")
    freq_by_urn <- {
      ru <- route_remaining
      dow <- as.character(ru$`Days of Operation` %||% NA_character_)
      dow_clean <- gsub("[^1-7]", "", dow)
      ff <- nzint(nchar(dow_clean))
      ff[!is.finite(ff) | ff <= 0L] <- 7L
      setNames(as.integer(ff), as.character(ru$`Unique Route Number`))
    }
    
    # Sliding windows over unique departures + synthetic anchors (AM, noon-ish, latest-anchored)
    span <- pmax(1L, as.integer(hours_cap %||% 6L)) * 60L
    s_latest   <- if (is.finite(latest_cap))   as.integer(latest_cap) - as.integer(span) else NA_integer_
    s_earliest <- if (is.finite(earliest_cap)) as.integer(earliest_cap)                   else NA_integer_
    s_mid      <- 12L*60L - as.integer(span) %/% 2L
    starts <- sort(unique(c(cand$DepMin, s_latest, s_earliest, s_mid)))
    starts <- starts[is.finite(starts) & starts >= 0L]
    if (!length(starts)) return(NULL)
    
    best_start <- starts[1]
    best_score <- -1L
    
    for (s in starts) {
      e <- s + span
      subset <- cand %>% dplyr::filter(DepMin >= s, DepMin <= e)
      if (!nrow(subset)) next
      
      # Per-row naive cap
      subset$row_cap <- pmin(per_f_cap, subset$remaining)
      
      # Cap by URN remaining (don’t allow multiple rows of same URN to exceed remaining)
      urn_cap <- subset %>%
        dplyr::group_by(`Unique Route Number`) %>%
        dplyr::summarise(potential = sum(row_cap), remaining = max(remaining), .groups="drop") %>%
        dplyr::mutate(use = pmin(potential, remaining))
      
      total_by_urn <- sum(urn_cap$use)
      
      # Month 3: limit by available bin room as well (upper bound)
      if (month == 3 && !is.null(bin_caps)) {
        by_bin <- subset %>%
          dplyr::group_by(bin) %>%
          dplyr::summarise(bin_need = sum(row_cap), .groups="drop") %>%
          dplyr::mutate(bin_need = ifelse(is.na(bin_need), 0L, bin_need))
        bin_limit <- 0L
        # Bin-aware scoring with zero-cap guard and tie-breaker (Month 3)
        room_vec <- setNames(
          vapply(c("wd_am","wd_pm","we_am","we_pm"), function(b) {
            if (is.null(assigned_bins) || is.null(bin_caps[[b]])) return(Inf)
            pmax(0L, as.integer(bin_caps[[b]]) - as.integer(assigned_bins[[b]] %||% 0L))
          }, integer(1)), c("wd_am","wd_pm","we_am","we_pm")
        )
        total_need <- sum(as.integer(by_bin$bin_need), na.rm = TRUE)
        need_zero  <- sum(as.integer(by_bin$bin_need[match(names(room_vec)[room_vec <= 0], by_bin$bin)]), na.rm = TRUE)
        zero_frac  <- if (total_need > 0L) need_zero / total_need else 0
        if (is.finite(zero_frac) && zero_frac >= 0.85) {
          score <- -Inf
        } else {
          bin_limit <- 0L
          for (b in names(room_vec)) {
            need_b <- by_bin$bin_need[match(b, by_bin$bin)]; if (is.na(need_b)) need_b <- 0L
            room_b <- room_vec[[b]]
            bin_limit <- as.integer(bin_limit + as.integer(min(as.integer(need_b), as.integer(room_b))))
          }
          base <- min(as.integer(total_by_urn), as.integer(bin_limit), as.integer(day_cap %||% 40L))
          # small tie-breaker toward bins with room
          align_bonus <- 0.001 * sum(pmin(as.integer(by_bin$bin_need), as.integer(room_vec)), na.rm = TRUE)
          score <- as.numeric(base) + as.numeric(align_bonus)
        }
      } else {
        
        # ---- Months 1–2: window steering + banded weights + projected ratio tie-break ----
        if (month %in% c(1L, 2L)) {
          # Base density score (unchanged)
          base <- min(as.integer(total_by_urn), as.integer(day_cap %||% 40L))
          
          # Window composition
          has_pm_in_win <- nrow(subset) > 0 && any(subset$DepMin >= 12L*60L)
          has_am_in_win <- nrow(subset) > 0 && any(subset$DepMin <  12L*60L)
          
          # Weekend/weekday for this day
          we_day <- day_name %in% WEEKEND_DAYS
          
          # Steering terms
          steer_we <- 0.0
          steer_am <- 0.0
          pool_penalty <- 0.0
          hard_guard <- 0.0
          
          # Current AM/PM counts + user targets
          cnt <- try(global_am_pm_counts(), silent = TRUE)
          tg  <- try(get_targets(),           silent = TRUE)
          
          if (is.list(cnt) && is.list(tg)) {
            tot_now <- as.integer(cnt$tot %||% 0L)
            
            # Progressive tightening as schedule fills (0.8 early -> 1.6 late)
            tighten <- 0.8 + 0.8 * pmin(1, tot_now / 80.0)
            
            # Side-specific current ratio and target (split-aware)
            if (!isTRUE(tg$split)) {
              am_t <- (as.numeric(tg$am_global %||% 45)) / 100
              cur  <- if (tot_now > 0) (as.numeric(cnt$am %||% 0L) / tot_now) else am_t
            } else if (we_day) {
              tot0 <- as.integer(cnt$tot_we %||% 0L); am0 <- as.integer(cnt$am_we %||% 0L)
              am_t <- (as.numeric(tg$am_we %||% 45)) / 100
              cur  <- if (tot0 > 0) am0 / tot0 else am_t
            } else {
              tot0 <- as.integer(cnt$tot_wd %||% 0L); am0 <- as.integer(cnt$am_wd %||% 0L)
              am_t <- (as.numeric(tg$am_wd %||% 45)) / 100
              cur  <- if (tot0 > 0) am0 / tot0 else am_t
            }
            
            if (is.finite(cur) && is.finite(am_t)) {
              gap <- abs(cur - am_t)
              # Tighter bands: 8% / 4%
              Bwin <- if (gap > 0.08) 4800.0 * tighten else if (gap > 0.04) 3200.0 * tighten else 1800.0 * tighten
              
              # Guardrail: when far off, avoid pure windows that worsen the gap
              if (gap > 0.04) {
                if (cur > am_t && has_am_in_win && !has_pm_in_win) hard_guard <- -1e9 # too AM-heavy → avoid pure AM
                if (cur < am_t && has_pm_in_win && !has_am_in_win) hard_guard <- -1e9 # too PM-heavy → avoid pure PM
              }
              
              # Use day_name (explicit arg) + current assignments to compute the day’s progress
              slot_used_i <- {
                asg <- get0("assignments", inherits = TRUE, ifnotfound = NULL)
                u <- 0L
                if (is.list(asg) && !is.null(asg[[day_name]])) {
                  df_asg <- asg[[day_name]]
                  if (is.data.frame(df_asg) && nrow(df_asg)) {
                    u <- as.integer(sum(as.integer(df_asg$`Assigned Surveys` %||% 0L), na.rm = TRUE))
                  }
                }
                u
              }
              min_i <- if (month %in% c(1L, 2L)) 30L else 0L
              
              if (slot_used_i >= min_i) {
                if (cur > (am_t + 0.04) && has_pm_in_win) steer_am <- steer_am + Bwin
                if (cur < (am_t - 0.04) && has_am_in_win)  steer_am <- steer_am + Bwin
              }
              
              # Projected-ratio tie-break: estimate how this window moves the ratio
              am_cap <- sum(as.integer(subset$row_cap[subset$DepMin <  12L*60L] %||% 0L), na.rm = TRUE)
              pm_cap <- sum(as.integer(subset$row_cap[subset$DepMin >= 12L*60L] %||% 0L), na.rm = TRUE)
              cap_sum <- as.numeric(am_cap + pm_cap)
              if (cap_sum > 0) {
                # Proportional estimate using window composition and base size
                am_add_est <- as.numeric(base) * (as.numeric(am_cap) / cap_sum)
                pm_add_est <- as.numeric(base) - am_add_est
                if (we_day) {
                  tot_side <- as.numeric(cnt$tot_we %||% 0L)
                  am_side  <- as.numeric(cnt$am_we  %||% 0L)
                  proj_cur <- if ((tot_side + am_add_est + pm_add_est) > 0)
                    ((am_side + am_add_est) / (tot_side + am_add_est + pm_add_est)) else am_t
                } else {
                  tot_side <- as.numeric(cnt$tot_wd %||% 0L)
                  am_side  <- as.numeric(cnt$am_wd  %||% 0L)
                  proj_cur <- if ((tot_side + am_add_est + pm_add_est) > 0)
                    ((am_side + am_add_est) / (tot_side + am_add_est + pm_add_est)) else am_t
                }
                curr_dev <- abs(cur - am_t); proj_dev <- abs(proj_cur - am_t)
                steer_am <- steer_am + (curr_dev - proj_dev) * 500.0 * tighten
                if (proj_dev > 0.10 && proj_dev > curr_dev) pool_penalty <- pool_penalty - 600.0 * tighten
              }
            }
          }
          
          score <- as.numeric(base) + as.numeric(steer_we) + as.numeric(steer_am) + as.numeric(pool_penalty) + as.numeric(hard_guard)
          # Scarcity-aware window bonus: favor windows containing low-frequency routes (days/week 1–3)
          subset$.__freq <- {
            urn <- as.character(subset$`Unique Route Number`)
            mf  <- as.integer(freq_by_urn[urn])
            mf[is.na(mf) | mf < 1L] <- 7L
            mf
          }
          lin_rarity_win <- (7L - pmin(7L, pmax(1L, subset$.__freq))) / 6.0
          rare_cap   <- sum(as.numeric(subset$row_cap) * as.numeric(lin_rarity_win), na.rm = TRUE)
          rare_bonus <- 1200.0 * rare_cap
          score <- score + as.numeric(rare_bonus)
        } else {
          # Fallback for any other month (kept identical to previous behavior)
          score <- min(as.integer(total_by_urn), as.integer(day_cap %||% 40L))
        }
      }
      if (isTRUE(controls$prior_intl)) {
        priority_urn <- suppressWarnings(as.integer(controls$priority_intl_urn %||% NA_integer_))
        if (is.finite(priority_urn) && is.data.frame(subset) && nrow(subset)) {
          urnv <- suppressWarnings(as.integer(subset$`Unique Route Number` %||% NA_integer_))
          has_pr <- any(is.finite(urnv) & (urnv == priority_urn))
          if (isTRUE(has_pr)) {
            rem_vec <- route_remaining$remaining[match(priority_urn, route_remaining$`Unique Route Number`)]
            rem <- suppressWarnings(max(as.integer(rem_vec), na.rm = TRUE))
            if (!is.finite(rem) || rem <= 0L) rem <- 0L
            if (rem > 0L) {
              score <- score + 50000.0
            }
          }
        }
      }
      if (score > best_score) {
        best_score <- score
        best_start <- s
      }
    }
    list(start = best_start, end = best_start + span)
  }
  # --- NEW: estimate URN usage inside a candidate window (no side effects) ---
  window_urn_usage <- function(df_day, start_min, end_min, route_remaining, day_cap, hours_cap,
                               controls, month, bin_caps, assigned_bins, day_name) {
    if (is.null(df_day) || !nrow(df_day)) {
      return(list(use_by_urn = integer(0), bin_add = c(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)))
    }
    cand <- df_day %>%
      dplyr::mutate(
        DepMin = vapply(`Departure Time`, parse_user_time, integer(1)),
        DepMin = ((DepMin %% 1440) + 1440) %% 1440
      ) %>%
      dplyr::filter(is.finite(DepMin), DepMin >= start_min, DepMin <= end_min)
    if (!nrow(cand)) return(list(use_by_urn = integer(0), bin_add = c(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)))
    
    per_f_cap <- as.integer(nzint(controls$per_flight_cap %||% 10L))
    rem_map   <- route_remaining %>% dplyr::select(`Unique Route Number`, remaining)
    cand <- cand %>% dplyr::left_join(rem_map, by="Unique Route Number")
    cand$remaining[is.na(cand$remaining)] <- 0L
    cand$row_cap <- pmin(per_f_cap, cand$remaining)
    cand$bin     <- mapply(flight_bin, cand$Day, cand$DepMin)
    
    urn_tab <- cand %>%
      dplyr::group_by(`Unique Route Number`) %>%
      dplyr::summarise(potential = sum(row_cap), remaining = max(remaining), .groups="drop") %>%
      dplyr::mutate(use = pmin(potential, remaining))
    total_possible <- sum(urn_tab$use)
    
    bin_limit <- 1000000000L  # avoid as.integer(Inf)
    if (month == 3 && !is.null(bin_caps)) {
      by_bin <- cand %>%
        dplyr::group_by(bin) %>%
        dplyr::summarise(bin_need = sum(row_cap), .groups="drop") %>%
        dplyr::mutate(bin_need = ifelse(is.na(bin_need), 0L, bin_need))
      bin_limit <- 0L
      for (b in c("wd_am","wd_pm","we_am","we_pm")) {
        need_b <- by_bin$bin_need[match(b, by_bin$bin)]; if (is.na(need_b)) need_b <- 0L
        room_b <- if (is.null(assigned_bins) || is.null(bin_caps[[b]])) Inf else
          pmax(0L, as.integer(bin_caps[[b]]) - as.integer(assigned_bins[[b]] %||% 0L))
        bin_limit <- bin_limit + as.integer(min(need_b, room_b))
      }
    }
    limit <- min(as.integer(total_possible), as.integer(day_cap %||% 40L), as.integer(bin_limit))
    if (!is.finite(limit) || limit <= 0L) {
      return(list(use_by_urn = integer(0), bin_add = c(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)))
    }
    
    u <- urn_tab$use
    if (sum(u) == 0) return(list(use_by_urn = integer(0), bin_add = c(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)))
    frac <- u / sum(u)
    alloc <- floor(frac * limit)
    leftover <- as.integer(limit - sum(alloc))
    if (leftover > 0) {
      order_idx <- order(frac * limit - alloc, decreasing = TRUE)
      for (k in seq_len(leftover)) {
        j <- order_idx[((k-1) %% length(order_idx)) + 1L]
        alloc[j] <- alloc[j] + 1L
      }
    }
    use_by_urn <- setNames(as.integer(alloc), as.character(urn_tab$`Unique Route Number`))
    
    # approximate Month-3 bin additions proportional to need
    bin_add <- c(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)
    if (month == 3 && !is.null(bin_caps)) {
      by_bin <- cand %>% dplyr::group_by(bin) %>%
        dplyr::summarise(bin_need = sum(row_cap), .groups="drop")
      by_bin$bin_need[is.na(by_bin$bin_need)] <- 0L
      total_need <- sum(by_bin$bin_need)
      if (total_need > 0) {
        for (b in names(bin_add)) {
          need_b <- by_bin$bin_need[match(b, by_bin$bin)]; if (is.na(need_b)) need_b <- 0L
          bin_add[b] <- as.integer(round(limit * (need_b / total_need)))
        }
        delta <- as.integer(limit - sum(bin_add))
        if (delta != 0L) {
          ord <- order(by_bin$bin_need, decreasing = TRUE)
          names_ord <- by_bin$bin[ord]; names_ord[is.na(names_ord)] <- ""
          names_ord <- names_ord[names_ord %in% names(bin_add)]
          if (length(names_ord)) {
            k <- 1L
            while (delta != 0L && k <= 1000L) {
              b <- names_ord[((k-1) %% length(names_ord)) + 1L]
              bin_add[b] <- bin_add[b] + sign(delta)
              delta <- delta - sign(delta); k <- k + 1L
            }
          }
        }
      }
    }
    list(use_by_urn = use_by_urn, bin_add = bin_add)
  }
  
  # --- choose different hard-hour windows for duplicate weekdays (pairwise for 2 slots) ---
  plan_multi_windows_for_day <- function(df_all, day_label, slot_indices, eff_dates, route_remaining,
                                         day_caps_by_index, hours_caps, controls, month, bin_caps,
                                         assigned_bins, latest_cap, hard_latest) {
    
    # Return map keyed by slot index as character
    res <- setNames(vector("list", length(slot_indices)), as.character(slot_indices))
    if (!length(slot_indices)) return(res)
    
    # Build candidate flights for this weekday (respect effective dates + latest hard cap)
    df_d <- df_all %>%
      dplyr::filter(Day == day_label, if (!is.null(eff_dates)) dep_date %in% eff_dates else TRUE) %>%
      dplyr::mutate(
        DepMin = vapply(`Departure Time`, parse_user_time, integer(1)),
        DepMin = ((DepMin %% 1440) + 1440) %% 1440
      ) %>%
      dplyr::filter(is.finite(DepMin))
    
    if (is.finite(latest_cap) && hard_latest) {
      df_d <- df_d %>% dplyr::filter(DepMin <= latest_cap)
    }
    if (!nrow(df_d)) return(res)
    
    # (8) Pre-sort once by DepMin so window indexing is cheap
    df_d <- df_d[order(df_d$DepMin), , drop = FALSE]
    
    all_times    <- sort(unique(df_d$DepMin))
    earliest_dep <- min(all_times)
    # Dynamic earliest bound shift to preserve PM capacity (Months 1–2)
    earliest_dep_dyn <- earliest_dep
    if (month %in% c(1,2)) {
      # Determine remaining AM/PM room from the global pools
      we_day <- day_label %in% WEEKEND_DAYS
      am_room <- 1e9L; pm_room <- 1e9L
      if (exists("ampm_left", inherits = TRUE)) {
        if (!isTRUE(am_controls$split)) {
          am_room <- as.integer(ampm_left$AM %||% 0L)
          pm_room <- as.integer(ampm_left$PM %||% 0L)
        } else {
          if (we_day) {
            am_room <- as.integer(ampm_left$AM_we %||% 0L)
            pm_room <- as.integer(ampm_left$PM_we %||% 0L)
          } else {
            am_room <- as.integer(ampm_left$AM_wk %||% 0L)
            pm_room <- as.integer(ampm_left$PM_wk %||% 0L)
          }
        }
      }
      tot_room <- as.integer(pmax(1L, am_room + pm_room))
      am_share_left <- as.numeric(am_room) / as.numeric(tot_room)
      # If AM room is scarce, push the earliest bound later to straddle PM
      if (is.finite(am_share_left)) {
        if (am_share_left < 0.25) {
          earliest_dep_dyn <- max(as.integer(earliest_dep_dyn), 630L)  # 10:30 AM
        } else if (am_share_left < 0.35) {
          earliest_dep_dyn <- max(as.integer(earliest_dep_dyn), 570L)  # 9:30 AM
        }
      }
    } else {
      earliest_dep_dyn <- earliest_dep
    }
    latest_dep   <- max(all_times)
    latest_lim   <- if (isTRUE(hard_latest) && is.finite(latest_cap)) as.integer(latest_cap) else Inf
    
    # Snapshot of assigned bins (for Month 3 nudges only)
    bins_base <- assigned_bins %||% list(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)
    room <- list(
      wd_am = if (!is.null(bin_caps)) as.integer((bin_caps$wd_am %||% Inf) - (bins_base$wd_am %||% 0L)) else Inf,
      wd_pm = if (!is.null(bin_caps)) as.integer((bin_caps$wd_pm %||% Inf) - (bins_base$wd_pm %||% 0L)) else Inf,
      we_am = if (!is.null(bin_caps)) as.integer((bin_caps$we_am %||% Inf) - (bins_base$we_am %||% 0L)) else Inf,
      we_pm = if (!is.null(bin_caps)) as.integer((bin_caps$we_pm %||% Inf) - (bins_base$we_pm %||% 0L)) else Inf
    )
    
    # --- HARD spacing greedy pack for a given window (Months 1–2) -------------
    simulate_spacing_pack <- function(df_win, start_min, end_min, route_remaining, day_cap, per_f_cap) {
      if (is.null(df_win) || !nrow(df_win)) {
        return(list(use_by_urn = integer(0), bin_add = c(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)))
      }
      
      # Normalize times and slice the 6h window
      win <- df_win
      if (!("DepMin" %in% names(win))) {
        win$DepMin <- vapply(win$`Departure Time`, parse_user_time, integer(1))
      }
      win$DepMin <- ((win$DepMin %% 1440) + 1440) %% 1440
      win <- win[is.finite(win$DepMin) & win$DepMin >= start_min & win$DepMin <= end_min, , drop = FALSE]
      if (!nrow(win)) {
        return(list(use_by_urn = integer(0), bin_add = c(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)))
      }
      
      # Join remaining by URN and compute row caps
      rem_map <- route_remaining %>% dplyr::select(`Unique Route Number`, remaining)
      win <- win %>% dplyr::left_join(rem_map, by = "Unique Route Number")
      win$remaining[is.na(win$remaining)] <- 0L
      per_f_cap <- as.integer(nzint(per_f_cap %||% 10L))
      win$row_cap <- pmin(per_f_cap, nzint(win$remaining))
      
      # Sort by time; keep simple concourse code and bin
      win$Concourse <- cclean(win$Concourse)
      win$bin <- mapply(flight_bin, win$Day, win$DepMin)
      win <- win[order(win$DepMin, na.last = TRUE), , drop = FALSE]
      
      n <- nrow(win)
      if (n == 0L) {
        return(list(use_by_urn = integer(0), bin_add = c(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)))
      }
      
      assigned <- integer(n)
      cap_left <- as.integer(day_cap %||% 40L)
      # 'clock' = earliest time we can take the next flight
      clock <- -Inf
      
      # Track per-URN remaining within this window so multiple flights of the
      # same route on the same day cannot exceed that route’s overall remaining.
      rem_by_urn <- setNames(as.integer(route_remaining$remaining %||% 0L),
                             as.character(route_remaining$`Unique Route Number`))
      
      i <- 1L
      while (i <= n && cap_left > 0L) {
        dep_i <- win$DepMin[i]
        
        # If this flight is before we're ready (spacing), skip it
        if (dep_i < clock) { i <- i + 1L; next }
        
        # Clamp by per-flight cap, day cap, AND the URN's remaining within-window
        urn_i_chr <- as.character(win$`Unique Route Number`[i])
        urn_left  <- as.integer(rem_by_urn[[urn_i_chr]] %||% 0L)
        S_i <- as.integer(min(win$row_cap[i] %||% 0L, cap_left, urn_left))
        if (S_i > 0L) {
          assigned[i] <- S_i
          
          # Advance readiness clock based on spacing after taking S_i here
          # (use immediate next row’s concourse to keep the spacing penalty conservative).
          conc_change_next <- if (i < n) isTRUE(win$Concourse[i] != win$Concourse[i + 1L]) else FALSE
          clock <- dep_i + spacing_after(S_i, concourse_change = conc_change_next)
          cap_left <- cap_left - S_i
          
          # Decrease local remaining for this URN so later flights of the same route
          # on this day/window cannot overshoot its needed total.
          rem_by_urn[[urn_i_chr]] <- as.integer(pmax(0L, urn_left - S_i))
        }
        i <- i + 1L
      }
      
      if (!any(assigned > 0L)) {
        return(list(use_by_urn = integer(0), bin_add = c(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)))
      }
      
      # Collapse to URN usage
      urn_ids <- win$`Unique Route Number`
      use_by_urn <- tapply(assigned, urn_ids, sum)
      use_by_urn <- use_by_urn[!is.na(names(use_by_urn))]
      use_by_urn <- as.integer(use_by_urn)
      names(use_by_urn) <- names(tapply(assigned, urn_ids, sum))
      
      # Per-bin adds for diagnostics/M3 nudges
      bins <- win$bin
      bin_add <- c(
        wd_am = as.integer(sum(assigned[bins == "wd_am"], na.rm = TRUE)),
        wd_pm = as.integer(sum(assigned[bins == "wd_pm"], na.rm = TRUE)),
        we_am = as.integer(sum(assigned[bins == "we_am"], na.rm = TRUE)),
        we_pm = as.integer(sum(assigned[bins == "we_pm"], na.rm = TRUE))
      )
      
      list(use_by_urn = use_by_urn, bin_add = bin_add)
    }
    
    # ---- window scoring helper -------------------------------------------------
    # (5) Accept a cached row-index vector 'cand_idx' so we don't refilter each time
    score_window <- function(start_min, end_min, route_tmp, bins_tmp, day_cap, hours_cap, cand_idx = NULL) {
      if (!is.finite(start_min) || !is.finite(end_min) || start_min > end_min) {
        return(list(score = -Inf, wu = list(use_by_urn = integer(0), bin_add = NULL)))
      }
      
      # Slice df_d once if indices provided (pure optimization; identical logic)
      df_for_wu <- if (length(cand_idx)) df_d[cand_idx, , drop = FALSE] else df_d
      
      # First, the existing fast upper-bound (bin-aware) estimator
      wu <- window_urn_usage(
        df_day = df_for_wu,
        start_min = start_min,
        end_min   = end_min,
        route_remaining = route_tmp,
        day_cap   = as.integer(day_cap %||% 40L),
        hours_cap = hours_cap,
        controls  = controls,
        month     = month,
        bin_caps  = bin_caps,
        assigned_bins = bins_tmp,
        day_name  = day_label
      )
      
      placed <- sum(wu$use_by_urn %||% integer(0))
      
      # Months 1–2: re-score the window with a HARD spacing simulation so we
      # choose a window that truly packs under spacing rather than raw density.
      if ((month %in% c(1L, 2L)) || isTRUE(input$enforce_spacing)) {
        per_f_cap <- as.integer(nzint(controls$per_flight_cap %||% 10L))
        sim <- simulate_spacing_pack(
          df_win         = df_for_wu,
          start_min      = start_min,
          end_min        = end_min,
          route_remaining= route_tmp,
          day_cap        = as.integer(day_cap %||% 40L),
          per_f_cap      = per_f_cap
        )
        if (length(sim$use_by_urn)) {
          placed <- as.integer(sum(sim$use_by_urn))
          # Override with the spacing-feasible usage and per-bin adds
          wu$use_by_urn <- sim$use_by_urn
          wu$bin_add    <- sim$bin_add
        }
      }
      
      # Zero-cap guard: reject windows dominated by bins with no remaining room (Month 3)
      if (month == 3 && !is.null(bin_caps) && length(wu$bin_add)) {
        rm_vec <- setNames(
          vapply(c("wd_am","wd_pm","we_am","we_pm"), function(b) {
            as.integer((bin_caps[[b]] %||% 0L) - as.integer(bins_tmp[[b]] %||% 0L))
          }, integer(1)), c("wd_am","wd_pm","we_am","we_pm")
        )
        total_need <- sum(as.integer(wu$bin_add %||% 0L), na.rm = TRUE)
        need_zero  <- sum(as.integer(wu$bin_add[names(rm_vec)[rm_vec <= 0]] %||% 0L), na.rm = TRUE)
        zero_frac  <- if (total_need > 0L) need_zero / total_need else 0
        if (is.finite(zero_frac) && zero_frac >= 0.85) return(list(score = -Inf, wu = wu))
      }
      
      # Gentle bin complement bonus (Month 3)
      bin_bonus <- 0
      if (month == 3 && !is.null(bin_caps) && length(wu$bin_add)) {
        for (b in names(wu$bin_add)) {
          rm <- as.integer((bin_caps[[b]] %||% 0L) - as.integer(bins_tmp[[b]] %||% 0L))
          if (is.finite(rm) && rm > 0L) {
            add <- as.integer(wu$bin_add[[b]] %||% 0L)
            if (add > 0L) bin_bonus <- bin_bonus + min(add, rm) * 0.25
          }
        }
      }
      
      # Edge coverage nudges (use same pre-slice for speed)
      cand_win <- if (length(cand_idx)) df_d[cand_idx, , drop = FALSE] else
        df_d %>% dplyr::filter(DepMin >= start_min, DepMin <= end_min)
      we_day <- day_label %in% c("Sat","Sun")
      has_pm_in_win <- isTRUE(nrow(cand_win) > 0) && isTRUE(any(as.integer(cand_win$DepMin) >= 12L*60L))
      has_am_in_win <- isTRUE(nrow(cand_win) > 0) && isTRUE(any(as.integer(cand_win$DepMin) <  12L*60L))
      
      safe_room_pm <- isTRUE(all(is.finite(as.integer(room$we_pm)))) && isTRUE(as.integer(room$we_pm) > 0L)
      safe_room_am <- isTRUE(all(is.finite(as.integer(room$we_am)))) && isTRUE(as.integer(room$we_am) > 0L)
      
      pm_bonus <- if (isTRUE(we_day) && isTRUE(month == 3L) && safe_room_pm && has_pm_in_win) 2.0 else 0
      am_bonus <- if (isTRUE(we_day) && isTRUE(month == 3L) && safe_room_am && has_am_in_win) 2.0 else 0
      if (nrow(cand_win)) {
        wmin_dep <- min(cand_win$DepMin); wmax_dep <- max(cand_win$DepMin)
      } else {
        wmin_dep <- NA_integer_; wmax_dep <- NA_integer_
      }
      near_start <- if (is.finite(wmin_dep)) pmax(0, 1 - (wmin_dep - earliest_dep) / 90) else 0
      near_end   <- if (is.finite(wmax_dep)) pmax(0, 1 - (latest_dep    - wmax_dep) / 90) else 0
      edge_bonus <- if (we_day) (1.2 * near_end + 0.6 * near_start) else (0.8 * (near_end + near_start))
      
      # Tie-breaker: small bonus toward windows that consume bins with room (Month 3)
      room_align_bonus <- 0
      if (month == 3 && !is.null(bin_caps) && length(wu$bin_add)) {
        rm_vec2 <- setNames(
          vapply(c("wd_am","wd_pm","we_am","we_pm"), function(b) {
            pmax(0L, as.integer((bin_caps[[b]] %||% 0L) - as.integer(bins_tmp[[b]] %||% 0L)))
          }, integer(1)), c("wd_am","wd_pm","we_am","we_pm")
        )
        room_align_bonus <- 0.001 * sum(pmin(as.integer(wu$bin_add), rm_vec2), na.rm = TRUE)
      }
      # --- Steering for Months 1–2: pull windows toward the needed buckets ---
      # If we are outside ±10% on Weekend% or AM%, give a big bonus to windows
      # that help (weekend day; or that contain AM/PM as needed).
      steer_we <- 0.0
      steer_am <- 0.0
      if (month %in% c(1, 2)) {
        cnt <- global_am_pm_counts()
        tot_now <- as.integer(cnt$tot %||% 0L)
        tg <- get_targets()
        # Tightened steering; skip heavy steering while the day is below its minimum floor
        # Compute per-day usage from current assignments (avoid relying on internal lists)
        slot_used_i <- {
          asg <- get0("assignments", inherits = TRUE, ifnotfound = NULL)
          u <- 0L
          if (is.list(asg) && !is.null(asg[[d]])) {
            df_asg <- asg[[d]]
            if (is.data.frame(df_asg) && nrow(df_asg)) {
              u <- as.integer(sum(as.integer(df_asg$`Assigned Surveys` %||% 0L), na.rm = TRUE))
            }
          }
          u
        }
        min_i <- if (month %in% c(1L, 2L)) 30L else 0L
        Bwin  <- if (slot_used_i < min_i) 0.0 else 9200.0
        
        if (is.finite(tot_now)) {
          # AM/PM steering — prefer windows that include the needed side
          if (!isTRUE(tg$split)) {
            am_t <- (as.numeric(tg$am_global %||% 45)) / 100
            cur_am <- if (tot_now > 0) (as.numeric(cnt$am %||% 0L) / tot_now) else am_t
            if (cur_am > (am_t + 0.06) && has_pm_in_win) steer_am <- Bwin  # too many AM → pick PM window
            if (cur_am < (am_t - 0.06) && has_am_in_win) steer_am <- Bwin  # too few AM → pick AM window
          } else {
            # Split targets
            if (we_day) {
              tot0 <- as.integer(cnt$tot_we %||% 0L); am0 <- as.integer(cnt$am_we %||% 0L)
              am_t <- (as.numeric(tg$am_we %||% 45)) / 100
              cur  <- if (tot0 > 0) am0 / tot0 else am_t
            } else {
              tot0 <- as.integer(cnt$tot_wd %||% 0L); am0 <- as.integer(cnt$am_wd %||% 0L)
              am_t <- (as.numeric(tg$am_wd %||% 45)) / 100
              cur  <- if (tot0 > 0) am0 / tot0 else am_t
            }
            if (cur > (am_t + 0.10) && has_pm_in_win)    steer_am <- Bwin
            if (cur < (am_t - 0.10) && has_am_in_win)    steer_am <- Bwin
          }
        }
      }
      host_bonus <- 0.0
      if (isTRUE(controls$prior_intl)) {
        priority_urn <- suppressWarnings(as.integer(controls$priority_intl_urn %||% NA_integer_))
        if (is.finite(priority_urn) && is.data.frame(cand_win) && nrow(cand_win)) {
          urnv <- suppressWarnings(as.integer(cand_win$`Unique Route Number` %||% NA_integer_))
          has_pr <- any(is.finite(urnv) & (urnv == priority_urn))
          if (isTRUE(has_pr)) {
            rem_vec <- route_tmp$remaining[match(priority_urn, route_tmp$`Unique Route Number`)]
            rem <- suppressWarnings(max(as.integer(rem_vec), na.rm = TRUE))
            if (!is.finite(rem) || rem <= 0L) rem <- 0L
            if (rem > 0L) {
              host_bonus <- 50000.0
            }
          }
        }
      }
      list(
        score = placed + bin_bonus + edge_bonus + pm_bonus + am_bonus +
          room_align_bonus + steer_we + steer_am + host_bonus,
        wu = wu
      )
    }
    
    # Build candidate windows for a slot (start-anchored and end-anchored)
    build_candidates_for_slot <- function(idx, route_tmp, bins_tmp) {
      span_max <- pmax(1L, as.integer(hours_caps[idx] %||% controls$max_hours %||% 6L)) * 60L
      cands <- list()
      
      # 1) start-anchored windows: [s, min(s+span_max, latest limit)]
      for (s in all_times) {
        e <- s + span_max
        if (is.finite(latest_lim)) e <- min(e, latest_lim)
        if (s <= e) cands[[length(cands)+1L]] <- c(start = s, end = e)
      }
      # 2) end-anchored windows: [max(e-span_max, earliest_dep_dyn), e]
      for (e in all_times) {
        if (is.finite(latest_lim) && e > latest_lim) next
        s <- max(e - span_max, earliest_dep_dyn)
        if (s <= e) cands[[length(cands)+1L]] <- c(start = s, end = e)
      }
      
      # Deduplicate
      if (length(cands)) {
        mat <- do.call(rbind, cands)
        dfw <- as.data.frame(mat)
        dfw <- dfw[!duplicated(dfw), , drop = FALSE]
      } else {
        dfw <- data.frame(start = integer(0), end = integer(0))
      }
      
      # Ensure sentinel windows (earliest-anchored, latest-anchored)
      sent_start <- data.frame(start = earliest_dep_dyn, end = earliest_dep_dyn + span_max)
      sent_end   <- data.frame(start = pmax(earliest_dep_dyn, latest_dep - span_max), end = latest_dep)
      if (is.finite(latest_lim)) {
        sent_start$end <- pmin(sent_start$end, latest_lim)
        sent_end$end   <- pmin(sent_end$end,   latest_lim)
      }
      dfw <- rbind(dfw, sent_start, sent_end)
      dfw <- dfw[!duplicated(dfw), , drop = FALSE]
      
      # (5) Precompute row indices for each window once
      dfw$idx <- lapply(seq_len(nrow(dfw)), function(i) {
        if (!nrow(df_d)) integer(0) else which(df_d$DepMin >= dfw$start[i] & df_d$DepMin <= dfw$end[i])
      })
      
      # Pre-score each window to select top-K and keep 'idx'
      if (nrow(dfw)) {
        scr <- vapply(seq_len(nrow(dfw)), function(i) {
          sw <- score_window(dfw$start[i], dfw$end[i], route_tmp, bins_tmp,
                             day_cap = day_caps_by_index[idx], hours_cap = hours_caps[idx],
                             cand_idx = dfw$idx[[i]])
          as.numeric(sw$score)
        }, numeric(1))
        dfw$pre_score <- scr
        
        # Keep the top-K windows; keep sentinel windows even if outside top-K
        K <- min(32L, nrow(dfw))
        ord  <- order(dfw$pre_score, decreasing = TRUE)
        keep <- ord[seq_len(K)]
        s1row <- which(dfw$start == sent_start$start & dfw$end == sent_start$end)
        s2row <- which(dfw$start == sent_end$start   & dfw$end == sent_end$end)
        keep  <- sort(unique(c(keep, s1row, s2row)))
        dfw   <- dfw[keep, c("start","end","pre_score","idx"), drop = FALSE]
      }
      dfw
    }
    
    # Build per-slot candidate sets
    route_base <- route_remaining
    per_slot_cands <- lapply(slot_indices, function(idx) build_candidates_for_slot(idx, route_base, bins_base))
    names(per_slot_cands) <- as.character(slot_indices)
    # DEBUG: candidate counts and top pre-scores per slot before combination
    {
      counts <- vapply(per_slot_cands, nrow, integer(1))
      top_pre <- vapply(per_slot_cands, function(dfw) {
        if (!nrow(dfw) || !("pre_score" %in% names(dfw))) return("")
        paste(utils::head(round(as.numeric(dfw$pre_score), 1), 5), collapse = ",")
      }, character(1))
      debug_note(day_label, NA, "combo_build_cands", list(
        Slots = paste(slot_indices, collapse = ","),
        per_slot_counts = paste(counts, collapse = "/"),
        per_slot_top_pre = paste(top_pre, collapse = " | ")
      ))
    }
    if (any(vapply(per_slot_cands, nrow, integer(1)) == 0L)) {
      debug_note(day_label, NA, "combo_no_candidates", list(
        Slots = paste(slot_indices, collapse = ","),
        per_slot_counts = paste(vapply(per_slot_cands, nrow, integer(1)), collapse = "/")
      ))
      return(res)
    }
    
    # Precompute base-state evaluations (reused when a slot is evaluated first)
    base_sw <- lapply(seq_along(per_slot_cands), function(j){
      dfw <- per_slot_cands[[j]]
      if (!nrow(dfw)) return(vector("list", 0L))
      lapply(seq_len(nrow(dfw)), function(i){
        score_window(dfw$start[i], dfw$end[i], route_base, bins_base,
                     day_cap = day_caps_by_index[slot_indices[[j]]],
                     hours_cap = hours_caps[slot_indices[[j]]],
                     cand_idx = dfw$idx[[i]])
      })
    })
    
    # Safe theoretical upper bound for total score (helps early exit)
    ub_max <- sum(vapply(per_slot_cands, function(dfw) max(as.numeric(dfw$pre_score) %||% 0), numeric(1))) + 2
    
    # (6) Fast URN→row mapping used in consumption updates (vectorized named lookup)
    route_pos <- setNames(seq_len(nrow(route_base)), as.character(route_base$`Unique Route Number`))
    
    # Enumerate combinations across duplicate slots and simulate usage
    overlap_penalty_per_min <- 0.01
    idx_lists <- lapply(per_slot_cands, function(dfw) seq_len(nrow(dfw)))
    grid <- as.matrix(expand.grid(idx_lists, KEEP.OUT.ATTRS = FALSE, stringsAsFactors = FALSE))
    if (!is.matrix(grid)) grid <- matrix(grid, nrow = 1)
    
    # Order combinations by optimistic sum of per-slot pre_scores (find strong best early)
    grid_pre <- vapply(seq_len(nrow(grid)), function(r){
      picks <- grid[r, ]
      sum(vapply(seq_along(slot_indices), function(j){
        as.numeric(per_slot_cands[[j]]$pre_score[as.integer(picks[[j]])] %||% 0)
      }, numeric(1)))
    }, numeric(1))
    ord_grid <- order(grid_pre, decreasing = TRUE)
    # DEBUG: size of combination grid and top 5 pre-sum scores
    {
      top5_pre <- utils::head(grid_pre[ord_grid], 5)
      debug_note(day_label, NA, "combo_grid", list(
        Slots = paste(slot_indices, collapse = ","),
        combos = as.integer(nrow(grid)),
        top5_pre = paste(round(top5_pre, 1), collapse = ","),
        ub_max = round(ub_max, 1)
      ))
    }
    best_total <- -Inf
    best_pick  <- NULL
    early_done <- FALSE
    for (r_idx in ord_grid) {
      pick_idx <- grid[r_idx, ]
      
      # Compose chosen windows for this combination
      wins <- lapply(seq_along(slot_indices), function(j) {
        dfw  <- per_slot_cands[[j]]
        ridx <- as.integer(pick_idx[j])
        if (!is.finite(ridx) || ridx < 1L || ridx > nrow(dfw)) ridx <- 1L
        dfw[ridx, , drop = FALSE]
      })
      
      # Overlap penalty minutes for this pair (or set)
      overlap_minutes <- 0
      if (length(wins) >= 2L) {
        for (a in 1:(length(wins)-1L)) for (b in (a+1L):length(wins)) {
          s1 <- wins[[a]]$start[[1]]; e1 <- wins[[a]]$end[[1]]
          s2 <- wins[[b]]$start[[1]]; e2 <- wins[[b]]$end[[1]]
          overlap_minutes <- overlap_minutes + max(0L, min(e1, e2) - max(s1, s2))
        }
      }
      
      # Both orders to reduce bias (unchanged)
      orders_to_try <- list(seq_along(slot_indices))
      if (length(slot_indices) == 2L) orders_to_try <- c(orders_to_try, list(rev(seq_along(slot_indices))))
      
      # Chosen windows' pre_scores for a safe bound
      chosen_pre_scores <- vapply(seq_along(slot_indices), function(j) {
        as.numeric(per_slot_cands[[j]]$pre_score[as.integer(pick_idx[j])] %||% 0)
      }, numeric(1))
      for (ord in orders_to_try) {
        route_tmp <- route_base
        bins_tmp  <- bins_base
        placed_sum_score <- 0
        comb_bin_add <- c(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)
        
        # Evaluate windows in the given order and simulate consumption
        for (step in seq_along(ord)) {
          k   <- ord[[step]]
          idx <- slot_indices[[k]]
          w   <- wins[[k]]
          
          # Use cached base-state evaluation for the first window in this order
          if (step == 1L) {
            ridx_first <- as.integer(pick_idx[k])
            sw <- base_sw[[k]][[ridx_first]]
          } else {
            sw <- score_window(w$start[[1]], w$end[[1]], route_tmp, bins_tmp,
                               day_cap = day_caps_by_index[idx], hours_cap = hours_caps[idx],
                               cand_idx = w$idx[[1]])
          }
          placed_here <- as.numeric(sw$score)
          placed_sum_score <- placed_sum_score + placed_here
          
          # Safe upper-bound prune
          if (step < length(ord)) {
            ub_remaining <- sum(chosen_pre_scores[ord[(step+1):length(ord)]])
            if ((placed_sum_score + ub_remaining) <= best_total) { placed_sum_score <- -Inf; break }
          }
          
          # Accumulate bin adds
          if (month == 3 && length(sw$wu$bin_add)) {
            for (b in names(comb_bin_add)) {
              comb_bin_add[[b]] <- as.integer(comb_bin_add[[b]] %||% 0L) + as.integer(sw$wu$bin_add[[b]] %||% 0L)
            }
          }
          
          # Simulate consumption using fast URN→row index
          if (length(sw$wu$use_by_urn)) {
            nn  <- names(sw$wu$use_by_urn)
            pos <- as.integer(route_pos[nn])
            keep <- !is.na(pos) & pos > 0L
            if (any(keep)) {
              dec <- as.integer(sw$wu$use_by_urn[keep])
              route_tmp$remaining[pos[keep]] <- pmax(0L, as.integer(route_tmp$remaining[pos[keep]]) - dec)
            }
          }
          if (month == 3 && !is.null(bin_caps) && length(sw$wu$bin_add)) {
            for (b in names(bins_tmp)) {
              bins_tmp[[b]] <- as.integer(bins_tmp[[b]] %||% 0L) + as.integer(sw$wu$bin_add[[b]] %||% 0L)
            }
          }
        }
        if (!is.finite(placed_sum_score)) next  # pruned
        
        # Base score and overlap penalty
        total_score <- placed_sum_score - overlap_penalty_per_min * overlap_minutes
        
        # Weekend AM/PM nudges
        if (day_label %in% c("Sat","Sun") && !is.null(bin_caps)) {
          has_we_am <- as.integer(comb_bin_add[["we_am"]] %||% 0L) > 0L
          has_we_pm <- as.integer(comb_bin_add[["we_pm"]] %||% 0L) > 0L
          room_we_am <- isTRUE(all(is.finite(as.integer(room$we_am)))) && isTRUE(as.integer(room$we_am) > 0L)
          room_we_pm <- isTRUE(all(is.finite(as.integer(room$we_pm)))) && isTRUE(as.integer(room$we_pm) > 0L)
          if (isTRUE(room_we_am) && isTRUE(has_we_am)) total_score <- total_score + 0.5
          if (isTRUE(room_we_pm) && isTRUE(has_we_pm)) total_score <- total_score + 1.0
        }
        if (total_score > best_total) {
          best_total <- total_score
          best_pick  <- wins
          if (best_total >= ub_max) { early_done <- TRUE; break }
        }
      } 
      if (isTRUE(early_done)) break
    }
    
    # Materialize best windows into the result map
    if (!is.null(best_pick)) {
      for (j in seq_along(slot_indices)) {
        res[[as.character(slot_indices[[j]])]] <- list(start = best_pick[[j]]$start[[1]],
                                                       end   = best_pick[[j]]$end[[1]])
      }
    }
    res
  }
  
  # ---- simple rebalancer (make room on a capped day) ----
  try_rebalance <- function(days, assignments, df_all, day_caps, controls, month, bin_caps){
    # Work by slot index (not day name) so duplicates like "Sun" are safe.
    hh_flags <- (state$hard_hours_flags %||% rep(FALSE, length(assignments)))
    per_day_totals <- vapply(seq_along(assignments), function(i) {
      x <- assignments[[i]]
      if (is.data.frame(x) && nrow(x)) sum(x$`Assigned Surveys`) else 0L
    }, integer(1))
    full_slots <- which(per_day_totals >= as.integer(day_caps))
    if (!length(full_slots)) return(assignments)
    for (i_d in full_slots) {
      df_d_sched <- assignments[[i_d]]
      if (!is.data.frame(df_d_sched) || !nrow(df_d_sched)) next
      
      # candidate target slots with room (exclude this same slot)
      targets <- setdiff(which(per_day_totals < as.integer(day_caps)), i_d)
      if (!length(targets)) next
      donors <- df_d_sched %>% dplyr::arrange(`Assigned Surveys`)
      for (r in seq_len(nrow(donors))) {
        row   <- donors[r, ]
        urn_v <- row$`Unique Route Number`
        
        # For each target slot, check if this URN operates on that slot's weekday
        possible <- list()
        for (i_t in targets) {
          tday <- days[i_t]
          have <- df_all %>% dplyr::filter(Day == tday, `Unique Route Number` == urn_v)
          if (nrow(have)) possible[[as.character(i_t)]] <- have
        }
        if (!length(possible)) next
        pick_key <- names(possible)[1]
        i_t <- as.integer(pick_key)
        have <- possible[[pick_key]]
        repl <- have[1, ]
        repl_row <- tibble::tibble(
          Day = days[i_t],
          Airline = repl$Airline, Concourse = repl$Concourse, Gate = NA_character_,
          Destination = repl$Destination, `Flight #` = repl$`Flight #`,
          `Departure Time` = to_ampm(repl$`Departure Time`),
          `Assigned Surveys` = row$`Assigned Surveys`,
          `Flight Type` = repl$`Flight Type`,
          `Airline Code` = repl$`Airline Code`,
          `Destination Code` = repl$`Destination Code`,
          `Unique Route Number` = urn_v,
          DepMin = repl$DepMin
        )
        slot_depmins <- if (is.data.frame(assignments[[i_t]]) && nrow(assignments[[i_t]])) {
          as.integer(assignments[[i_t]]$DepMin)
        } else integer(0)
        new_depmins <- c(slot_depmins, as.integer(repl_row$DepMin))
        
        # hours cap for the target slot i_t (fine-tune > global > default 6)
        cap_hours_t <- if (isTRUE(input$fine_tune_days) && !is.null(input[[paste0("ft_hours_", i_t)]])) {
          as.integer(input[[paste0("ft_hours_", i_t)]])
        } else {
          as.integer(controls$max_hours %||% input$max_hours %||% 6L)
        }
        if (is.na(cap_hours_t) || cap_hours_t <= 0L) cap_hours_t <- 6L
        # In Months 1–2, enforce hours span strictly (ignore slot hard-hours toggle).
        # In other months, keep existing behavior.
        span_ok <- if (month %in% c(1L, 2L)) {
          length(new_depmins) <= 1L ||
            (max(new_depmins) - min(new_depmins) <= cap_hours_t * 60L)
        } else {
          !isTRUE(hh_flags[i_t]) ||
            length(new_depmins) <= 1L ||
            (max(new_depmins) - min(new_depmins) <= cap_hours_t * 60L)
        }
        # Enforce interflight spacing HARD during rebalancing for Months 1–2
        spacing_ok_t <- TRUE
        if (month %in% c(1,2)) {
          sched_t <- assignments[[i_t]]
          if (!is.data.frame(sched_t)) sched_t <- tibble::tibble()
          # preview schedule with the proposed row
          sched_t <- dplyr::bind_rows(sched_t, repl_row) %>%
            dplyr::arrange(DepMin)
          dep  <- as.integer(sched_t$DepMin)
          conc <- cclean(sched_t$Concourse)
          Sv   <- as.integer(sched_t$`Assigned Surveys`)
          # position of the proposed row (match by URN + DepMin; fallback by DepMin)
          pos <- which(sched_t$`Unique Route Number` == urn_v & dep == as.integer(repl_row$DepMin))[1]
          if (is.na(pos) || !is.finite(pos)) pos <- which(dep == as.integer(repl_row$DepMin))[1]
          if (is.finite(pos)) {
            spacing_ok_prev <- TRUE
            spacing_ok_next <- TRUE
            if (pos > 1) {
              need_prev <- spacing_after(Sv[pos-1], conc[pos-1] != conc[pos])
              spacing_ok_prev <- dep[pos] >= (dep[pos-1] + as.integer(need_prev))
            }
            if (pos < length(dep)) {
              need_next <- spacing_after(Sv[pos], conc[pos] != conc[pos+1])
              spacing_ok_next <- dep[pos+1] >= (dep[pos] + as.integer(need_next))
            }
            spacing_ok_t <- isTRUE(spacing_ok_prev) && isTRUE(spacing_ok_next)
          }
        }
        
        # Only move if the target slot stays within its cap AND (Month 3) bin cap
        bin_ok <- TRUE
        if (month == 3 && !is.null(bin_caps)) {
          b_to <- flight_bin(as.character(days[i_t]), as.integer(repl_row$DepMin))
          if (is.character(b_to) && nzchar(b_to) &&
              !is.null(bin_caps[[b_to]]) && is.finite(as.numeric(bin_caps[[b_to]]))) {
            # Count current usage in the target bin across all slots
            used_now <- 0L
            for (kk in seq_along(assignments)) {
              dfk <- assignments[[kk]]
              if (is.data.frame(dfk) && nrow(dfk)) {
                dname_k <- as.character(days[kk])
                depmins_k <- as.integer(dfk$DepMin)
                bins_k <- vapply(depmins_k, function(m) flight_bin(dname_k, m), character(1))
                used_now <- used_now + sum(dfk$`Assigned Surveys`[bins_k == b_to], na.rm = TRUE)
              }
            }
            # If moving within the same bin, exclude the donor row we're about to remove
            b_from <- flight_bin(as.character(days[i_d]), as.integer(row$DepMin))
            if (identical(b_from, b_to)) {
              used_now <- used_now - as.integer(repl_row$`Assigned Surveys`)
            }
            cap_to <- as.integer(bin_caps[[b_to]] %||% 0L)
            bin_ok <- (used_now + as.integer(repl_row$`Assigned Surveys`)) <= cap_to
          }
        }
        
        if (sum(assignments[[i_t]]$`Assigned Surveys`) + repl_row$`Assigned Surveys` <= as.integer(day_caps[i_t]) &&
            span_ok && spacing_ok_t && isTRUE(bin_ok)) {
          # remove from donor slot
          idx_rm <- which(df_d_sched$`Unique Route Number` == urn_v & df_d_sched$DepMin == row$DepMin)[1]
          if (!is.na(idx_rm)) {
            df_d_sched <- df_d_sched[-idx_rm, , drop = FALSE]
            assignments[[i_d]] <- df_d_sched
            
            # add to target slot
            assignments[[i_t]] <- dplyr::bind_rows(assignments[[i_t]], repl_row) %>%
              dplyr::arrange(DepMin, Concourse, Airline)
            # Month-3: keep realized bin counters in sync for rebalanced moves
            if (month == 3) {
              b_from <- flight_bin(as.character(days[i_d]), as.integer(row$DepMin))
              b_to   <- flight_bin(as.character(days[i_t]), as.integer(repl_row$DepMin))
              if (is.character(b_from) && nzchar(b_from)) {
                live_bins_loc[[b_from]] <- as.integer(live_bins_loc[[b_from]] %||% 0L) - as.integer(repl_row$`Assigned Surveys`)
              }
              if (is.character(b_to) && nzchar(b_to)) {
                live_bins_loc[[b_to]] <- as.integer(live_bins_loc[[b_to]] %||% 0L) + as.integer(repl_row$`Assigned Surveys`)
              }
            }
            # update running totals
            per_day_totals[i_d] <- if (nrow(assignments[[i_d]])) sum(assignments[[i_d]]$`Assigned Surveys`) else 0L
            per_day_totals[i_t] <- if (nrow(assignments[[i_t]])) sum(assignments[[i_t]]$`Assigned Surveys`) else 0L
            break
          }
        }
      }
    }
    assignments
  }
  
  # ---------------------- Generate ----------------------
  observeEvent(input$generate, {
    req(input$file)
    
    # Key equality for Date Fit without creating suffixed names
    schedule_keys_equal <- function(need_keys, have_keys){
      # Prefer code-based matches if both code columns aren’t all NA
      use_codes <- !all(is.na(need_keys$`Airline Code`)) && !all(is.na(need_keys$`Destination Code`))
      if (use_codes) {
        want <- need_keys %>% dplyr::select(`Airline Code`,`Destination Code`,`Flight #`) %>% dplyr::distinct()
        got  <- have_keys %>% dplyr::select(`Airline Code`,`Destination Code`,`Flight #`) %>% dplyr::distinct()
        return(nrow(dplyr::semi_join(want, got, by = c("Airline Code","Destination Code","Flight #"))) == nrow(want))
      } else {
        want <- need_keys %>% dplyr::select(Airline, Destination, `Flight #`) %>% dplyr::distinct()
        got  <- have_keys %>% dplyr::select(Airline, Destination, `Flight #`) %>% dplyr::distinct()
        return(nrow(dplyr::semi_join(want, got, by = c("Airline","Destination","Flight #"))) == nrow(want))
      }
    }
    # Collect "spacing/hours prevented placement" by day (we'll group later)
    spacing_or_hours_blocked <- new.env(parent = emptyenv())
    spacing_or_hours_blocked$by_day <- list()
    add_spacing_hours_block <- function(day_name, urn_vec) {
      if (length(urn_vec) == 0) return(invisible(NULL))
      urn_vec <- as.integer(urn_vec[is.finite(as.integer(urn_vec))])
      if (!length(urn_vec)) return(invisible(NULL))
      if (is.null(spacing_or_hours_blocked$by_day[[day_name]]))
        spacing_or_hours_blocked$by_day[[day_name]] <- integer(0)
      spacing_or_hours_blocked$by_day[[day_name]] <- unique(c(spacing_or_hours_blocked$by_day[[day_name]], urn_vec))
      invisible(NULL)
    }
    # Build contiguous chains of spacing-bypass flights per selected slot/day
    compute_spacing_chains <- function(schedules, days) {
      out <- list()
      for (i in seq_along(schedules)) {
        df_i <- schedules[[i]]
        if (!is.data.frame(df_i) || nrow(df_i) < 2) next
        df_i <- dplyr::arrange(df_i, DepMin)
        
        node_label <- function(row) {
          ac <- as.character(row[["Airline Code"]] %||% row[["Airline"]] %||% "")
          dc <- as.character(row[["Destination Code"]] %||% row[["Destination"]] %||% "")
          paste0(ac, "/", dc)
        }
        
        chains <- list()
        cur <- character(0)
        
        for (j in 2:nrow(df_i)) {
          prev <- df_i[j-1, , drop = FALSE]
          curr <- df_i[j,   , drop = FALSE]
          
          prev_dep <- as.integer(prev$DepMin %||% NA_integer_)
          curr_dep <- as.integer(curr$DepMin %||% NA_integer_)
          if (!is.finite(prev_dep) || !is.finite(curr_dep)) next
          
          conc_change <- cclean(prev$Concourse) != cclean(curr$Concourse)
          need_gap    <- spacing_after(as.integer(prev$`Assigned Surveys` %||% 0L), conc_change)
          is_violate  <- curr_dep < (prev_dep + need_gap)
          
          if (is_violate) {
            prev_lab <- node_label(prev)
            curr_lab <- node_label(curr)
            if (length(cur) == 0) {
              cur <- c(prev_lab, curr_lab)
            } else {
              # continue the chain if it lines up, otherwise finalize and start new
              if (tail(cur, 1) != prev_lab) {
                if (length(cur) > 1) chains[[length(chains) + 1L]] <- cur
                cur <- c(prev_lab, curr_lab)
              } else {
                cur <- c(cur, curr_lab)
              }
            }
          } else {
            if (length(cur) > 1) chains[[length(chains) + 1L]] <- cur
            cur <- character(0)
          }
        }
        if (length(cur) > 1) chains[[length(chains) + 1L]] <- cur
        
        if (length(chains)) {
          out[[paste0(days[i], " (", i, ")")]] <- vapply(
            chains,
            function(ch) paste0("(", paste(ch, collapse = "->"), ")"),
            character(1)
          )
        }
      }
      out
    }
    
    tryCatch({
      state$unscheduled_reasons <- character(0)   # reset; we'll rebuild reasons below
      debug_reset()
      
      # --- Quick debug breadcrumbs (console) --------------------------------
      cat("\n=== GENERATE START ===\n")
      cat("Sheets:", paste(readxl::excel_sheets(input$file$datapath), collapse=", "), "\n")
      
      # --- Inputs / base data -----------------------------------------------
      df <- flights_df()
      rr <- routes_remaining()
      nf <- req_no_flights()
      
      # Sanity: chosen days & available flights
      days <- selected_days()
      if (!length(days)) {
        showNotification("Please select at least one day.", type = "error")
        return()
      }
      
      # Date filters precheck (slot-specific: each chosen Day 1–4 must have ≥1 date)
      if (isTRUE(input$restrict_dates_master)) {
        slot_labels <- c(input$day1, input$day2, input$day3, input$day4)
        slot_idx    <- which(slot_labels %in% DAY_LEVELS)
        empty_slots <- character(0)
        if (length(slot_idx)) {
          for (k in seq_along(slot_idx)) {
            idx_k   <- slot_idx[k]
            d       <- slot_labels[idx_k]
            input_id <- paste0("dates_slot", idx_k)
            allowed  <- input[[input_id]] %||% character(0)
            if (length(allowed) == 0) {
              empty_slots <- c(
                empty_slots,
                paste0("Day ", idx_k, " (", d, ")")
              )
            }
          }
        }
        if (length(empty_slots)) {
          showNotification(
            paste0(
              "No usable dates selected for: ",
              paste(empty_slots, collapse = ", "),
              ". Select at least one date for each chosen day."
            ),
            type = "error", duration = 10
          )
          return()
        }
      }
      empty_days2 <- vapply(days, function(d) nrow(df %>% dplyr::filter(Day == d)) == 0, logical(1))
      if (any(empty_days2)) {
        showNotification(
          paste0("No flights found for: ", paste(days[empty_days2], collapse = ", "), ". Pick different day(s)."),
          type = "error", duration = 10
        )
        return()
      }
      month <- as.integer(input$month_index %||% 1L)
      
      # Base remaining per URN from Routes Remaining (include all routes EXCEPT those with no flights in the current month)
      no_flight_urns <- if (is.null(nf)) integer(0) else unique(nzint(nf$`Unique Route Number`))
      route_base <- rr %>%
        dplyr::filter(!`Unique Route Number` %in% no_flight_urns) %>%
        dplyr::transmute(
          `Unique Route Number`,
          remaining = nzint(`Assigned Surveys`),  # remaining = surveys still needed
          Airline, Destination, `Flight Type`,
          `Airline Code`, `Destination Code`, `Days of Operation`
        )
      # Frequency heuristic from flight tabs
      # Frequency heuristic from Days of Operation (count 1–7 digits in the string)
      route_freq <- route_base %>%
        dplyr::transmute(
          `Unique Route Number`,
          freq = nchar(gsub("[^1-7]", "", as.character(`Days of Operation` %||% "")))
        )
      
      # Month 1–2 scarcity based on count of Days of Operation (1–7 digits present)
      # Daily (1234567) = 7 (lowest rarity); single-day (e.g., ..3....) = 1 (highest rarity).
      scarcity_m12 <- if (month %in% c(1,2)) {
        route_base %>%
          dplyr::transmute(
            `Unique Route Number`,
            scarcity_n = nchar(gsub("[^1-7]", "", as.character(`Days of Operation` %||% "")))
          )
      } else {
        NULL
      }
      priority_intl_urn <- NA_integer_
      if (isTRUE(input$prior_intl)) {
        intl_pool <- tryCatch({
          route_base %>%
            dplyr::filter(
              tolower(as.character(`Flight Type` %||% "")) == "international",
              as.integer(remaining %||% 0L) > 0L
            ) %>%
            dplyr::left_join(route_freq, by = "Unique Route Number")
        }, error = function(e) NULL)
        if (is.data.frame(intl_pool) && nrow(intl_pool)) {
          intl_pool <- intl_pool %>%
            dplyr::mutate(
              rem_int  = as.integer(remaining %||% 0L),
              freq_int = as.integer(freq %||% 7L)
            ) %>%
            dplyr::arrange(
              dplyr::desc(rem_int),    # most remaining surveys first
              freq_int,                # then most infrequent (fewest days)
              `Unique Route Number`    # then lowest URN
            )
          priority_intl_urn <- suppressWarnings(as.integer(intl_pool$`Unique Route Number`[1]))
        }
      }
      state$priority_intl_urn <- priority_intl_urn
      
      # ---- Caps: per-day caps and Month 3 bin caps -------------------------
      # Per-day cap is ALWAYS 40 unless fine-tune is ON and a number is entered
      if (isTRUE(input$fine_tune_days)) {
        day_caps <- sapply(seq_along(days), function(i){
          v <- input[[paste0("ft_surveys_", i)]]
          if (is.null(v) || is.na(v) || v == "") 40L else min(40L, nzint(v))
        })
      } else {
        day_caps <- rep(40L, length(days))
      }
      names(day_caps) <- days
      
      # ---- Minimum surveys per day (define early) ----
      min_per_day <- setNames(rep(0L, length(days)), days)
      if (isTRUE(input$fine_tune_days)) {
        for (i in seq_along(days)) {
          if (isTRUE(input[[paste0("min_toggle_", i)]])) {
            v <- nzint(input[[paste0("min_", i)]])
            if (is.finite(v) && v > 0L) min_per_day[i] <- v
          }
        }
      }
      # Enforce default per-day minimum of 30 for Months 1–2 (after capping by per-day caps)
      if (month %in% c(1L, 2L)) {
        min_per_day <- setNames(pmax(as.integer(min_per_day), 30L), days)
      }
      
      # Month 3 bin caps (max desired)
      wk_present <- any(days %in% WEEKEND_DAYS)
      bin_caps <- if (month == 3) list(
        wd_am = nzint(input$m3_wd_am), wd_pm = nzint(input$m3_wd_pm),
        we_am = if (wk_present) nzint(input$m3_we_am) else 0L,
        we_pm = if (wk_present) nzint(input$m3_we_pm) else 0L
      ) else NULL
      
      # ---- AM/PM Global Pools (HARD CEILINGS for Months 1–2) ------------------
      tg <- get_targets()
      # Fast upper bound on total surveys we could place: sum of per-slot caps
      MaxPotential <- sum(as.integer(day_caps))
      
      # Total surveys actually needed across all routes (exclude no-flight URNs already filtered)
      TotalNeeded <- sum(as.integer(route_base$remaining), na.rm = TRUE)
      
      # Realistic scheduling target = min(what we could place, what we actually need)
      SchedTarget <- as.integer(min(MaxPotential, TotalNeeded))
      
      # Split-aware totals by weekday/weekend (raw)
      wd_idx <- which(!(days %in% WEEKEND_DAYS))
      we_idx <- which(days %in% WEEKEND_DAYS)
      tot_wd <- if (length(wd_idx)) sum(as.integer(day_caps[wd_idx])) else 0L
      tot_we <- if (length(we_idx)) sum(as.integer(day_caps[we_idx])) else 0L
      
      # Pro-rate weekday/weekend capacity against the realistic target
      denom <- as.integer(tot_wd + tot_we)
      tot_wd_sched <- as.integer(if (denom > 0L) floor((tot_wd / denom) * SchedTarget) else 0L)
      tot_we_sched <- as.integer(max(0L, SchedTarget - tot_wd_sched))
      
      if (month %in% c(1,2)) {
        if (!tg$split) {
          # Global caps with ±10% band on the user's AM slider
          am_cap <- floor(((tg$am_global + 10) / 100) * SchedTarget)
          pm_cap <- floor(((100 - pmax(0, tg$am_global - 10)) / 100) * SchedTarget)
          ampm_left  <- list(
            AM    = as.integer(am_cap),
            PM    = as.integer(pm_cap),
            AM_wk = 1e9L, PM_wk = 1e9L,
            AM_we = 1e9L, PM_we = 1e9L
          )
          am_controls <- list(split = FALSE)
        } else {
          # Separate weekday/weekend caps with ±10% band on each slider
          # Correct AM/PM band math: enforce that PM cannot exceed
          # the complement of the *minimum* AM allowed by tolerance.
          tol <- 10 # percent wiggle
          
          # Weekday band
          am_wd_upper <- floor(((tg$am_wd + tol) / 100) * tot_wd_sched)
          am_wd_lower <- ceiling((pmax(0, tg$am_wd - tol) / 100) * tot_wd_sched)
          pm_wd_upper <- floor(((100 - (tg$am_wd - tol)) / 100) * tot_wd_sched)  # PM complement vs AM lower
          
          # Weekend band
          am_we_upper <- floor(((tg$am_we + tol) / 100) * tot_we_sched)
          am_we_lower <- ceiling((pmax(0, tg$am_we - tol) / 100) * tot_we_sched)
          pm_we_upper <- floor(((100 - (tg$am_we - tol)) / 100) * tot_we_sched)
          
          # Pools: we enforce *upper* caps for both AM and PM; the PM caps are tight
          # enough to force at least the AM lower bound once totals approach capacity.
          ampm_left <- list(
            AM    = 1e9L, PM = 1e9L,               # global not used when split=TRUE
            AM_wk = as.integer(am_wd_upper),       # AM cannot exceed its upper band
            PM_wk = as.integer(pm_wd_upper),       # PM cannot exceed complement of AM lower
            AM_we = as.integer(am_we_upper),
            PM_we = as.integer(pm_we_upper)
          )
          
          am_controls <- list(split = TRUE)
        }
      } else {
        # Month 3: no AM/PM pools (bin caps govern); give huge pools to avoid limiting
        ampm_left <- list(AM = 1e9L, PM = 1e9L, AM_wk = 1e9L, PM_wk = 1e9L, AM_we = 1e9L, PM_we = 1e9L)
        am_controls <- list(split = FALSE)
      }
      # ---- Single-slot override ----------------------------------------------------
      # If the user selected exactly one day/slot, disable AM/PM pools so we don't "save" for non-existent slots.
      if (length(days) == 1L) {
        ampm_left  <- list(AM = 1e9L, PM = 1e9L, AM_wk = 1e9L, PM_wk = 1e9L,
                           AM_we = 1e9L, PM_we = 1e9L)
        am_controls <- list(split = FALSE)
      }
      # Enforce AM/PM as hard caps during placement for Months 1–2
      hard_ampm <- (month %in% c(1,2))
      
      controls <- list(
        prior_intl        = input$prior_intl,
        prior_infreq      = input$prior_infreq,
        per_flight_cap    = nzint(input$per_flight_cap %||% 10L),
        earliest_dep      = input$earliest_dep,
        latest_dep        = input$latest_dep,
        max_hours         = input$max_hours,
        opt_compact       = TRUE,         # ← always on
        hard_earliest     = isTRUE(input$hard_earliest),
        hard_latest       = isTRUE(input$hard_latest),
        priority_intl_urn = priority_intl_urn
      )
      state$latest_cap_min <- if (isTRUE(input$hard_latest))   parse_user_time(input$latest_dep)   else parse_user_time("11:59 PM")
      state$earliest_cap_min <- if (isTRUE(input$hard_earliest)) parse_user_time(input$earliest_dep) else parse_user_time("5:00 AM")
      
      # Hard-hours flags
      hard_hours_flags <- vapply(seq_along(days), function(i){
        if (month %in% c(1,2)) {
          TRUE
        } else if (month == 3L) {
          if (isTRUE(input$fine_tune_days)) {
            v <- nzint(input[[paste0('ft_hours_', i)]])
            is.finite(v) && v > 0L
          } else {
            isTRUE(input$m3_hard_hours)
          }
        } else {
          FALSE
        }
      }, logical(1))
      state$hard_hours_flags <- hard_hours_flags
      
      min_per_day <- setNames(rep(0L, length(days)), days)
      # Allowed dates (from UI date filters)
      allowed_dates_for <- function(d){
        if (!isTRUE(input$restrict_dates_master)) return(NULL)
        
        # Date filters are stored per chosen Day-slot (dates_slot1..dates_slot4), not per weekday name.
        slot_labels <- c(input$day1, input$day2, input$day3, input$day4)
        slot_idx    <- which(slot_labels %in% DAY_LEVELS)
        if (!length(slot_idx)) return(NULL)
        
        # Find the first slot (in schedule order) that matches this weekday label.
        pos <- which(slot_labels[slot_idx] == d)
        if (!length(pos)) return(NULL)
        
        slot_no <- slot_idx[pos[1]]
        sel <- input[[paste0("dates_slot", slot_no)]] %||% character(0)
        if (!length(sel)) NULL else as.Date(sel)
      }
      
      # ---- GLOBAL INTERLEAVED SCHEDULER (multi-start, order-invariant) ----
      run_global_once <- function(jitter_sd = 0, seed = NULL) {
        if (!is.null(seed)) set.seed(seed)
        
        assignments <- vector("list", length(days)); names(assignments) <- days
        route_remaining_local <- route_base
        route_initial_remaining <- route_base
        route_used_count <- setNames(rep(0L, nrow(route_base)), as.character(route_base$`Unique Route Number`))
        urn_lock <- new.env(parent = emptyenv()); urn_lock$lock <- list()
        
        bypass_acc_loc <- new.env(parent = emptyenv())
        bypass_acc_loc$spacing_pairs <- list()
        bypass_acc_loc$daily_hours_days <- character(0)
        bypass_acc_loc$hard_hours_blocked <- list()
        bypass_acc_loc$last_meta <- list()
        
        live_bins_loc <- list(wd_am=0L, wd_pm=0L, we_am=0L, we_pm=0L)
        
        day_hours_caps <- sapply(seq_along(days), function(i){
          if (isTRUE(input$fine_tune_days)) {
            v <- nzint(input[[paste0("ft_hours_", i)]])
            if (!is.finite(v) || v <= 0L) 24L else v
          } else {
            v <- nzint(input$max_hours)
            if (!is.finite(v) || v <= 0L) 6L else v
          }
        })
        
        # Effective caps: when a checkbox is OFF, neutralize by using extreme bounds.
        latest_cap <- if (isTRUE(controls$hard_latest))   parse_user_time(controls$latest_dep)   else parse_user_time("11:59 PM")
        earliest_cap <- if (isTRUE(controls$hard_earliest)) parse_user_time(controls$earliest_dep) else parse_user_time("5:00 AM")
        hard_earliest_applies <- isTRUE(controls$hard_earliest)
        hard_latest_applies   <- isTRUE(controls$hard_latest)
        per_f_cap <- as.integer(nzint(controls$per_flight_cap %||% 10L))
        # --- Global AM/PM counters for hard-cap feasibility (Months 1/2 only) ---
        global_am <- 0L
        global_pm <- 0L
        current_bin_pools <- function(day_name) {
          if (!(as.integer(input$month_index) %in% c(1,2))) return(list(AM = 0L, PM = 0L))
          if (!isTRUE(am_controls$split)) list(AM = ampm_left$AM %||% 0L, PM = ampm_left$PM %||% 0L) else
            if (is_weekend(day_name)) list(AM = ampm_left$AM_we %||% 0L, PM = ampm_left$PM_we %||% 0L)
          else                      list(AM = ampm_left$AM_wk %||% 0L, PM = ampm_left$PM_wk %||% 0L)
        }
        
        # Running global AM/PM counts from current assignments
        global_am_pm_counts <- function() {
          am <- 0L; tot <- 0L; am_wd <- 0L; tot_wd <- 0L; am_we <- 0L; tot_we <- 0L
          for (nm in names(assignments)) {
            df_asg <- assignments[[nm]]
            if (!is.null(df_asg) && nrow(df_asg)) {
              k <- as.integer(sum(as.integer(df_asg$`Assigned Surveys` %||% 0L)))
              if (is.finite(k) && k > 0L) {
                mins <- vapply(df_asg$`Departure Time`, parse_user_time, integer(1))
                is_am_asg <- is.finite(mins) & (mins < 12*60)
                amc <- as.integer(sum(as.integer(df_asg$`Assigned Surveys`[is_am_asg] %||% 0L)))
                tot <- tot + k; am <- am + amc
                if (is_weekend(nm)) { tot_we <- tot_we + k; am_we <- am_we + amc } else { tot_wd <- tot_wd + k; am_wd <- am_wd + amc }
              }
            }
          }
          list(am=am, tot=tot, am_wd=am_wd, tot_wd=tot_wd, am_we=am_we, tot_we=tot_we)
        }
        # --- Band targets & helpers (Months 1–2) ---
        band_threshold <- 12L
        
        get_targets <- function() {
          we <- as.numeric(input$weekend_pct %||% 0)
          we <- max(0,min(100,we))
          split <- isTRUE(input$split_week_wknd)
          if (!split) {
            am_g <- as.numeric(input$am_pct %||% 45)
            am_g <- max(0,min(100,am_g))
            list(weekend = we, split = FALSE, am_global = am_g)
          } else {
            am_wd <- as.numeric(input$am_pct_wd %||% 45)
            am_we <- as.numeric(input$am_pct_we %||% 45)
            list(weekend = we, split = TRUE, am_wd = max(0,min(100,am_wd)), am_we = max(0,min(100,am_we)))
          }
        }
        
        would_violate_bands <- function(is_we, is_am, k) {
          cnt <- global_am_pm_counts()
          tot <- as.integer(cnt$tot %||% 0L)
          tot_n <- as.integer(tot + k)
          if (tot < band_threshold || k <= 0L) return(FALSE)
          
          if (month %in% c(1L, 2L)) {
            # Try to infer the current day label from the caller’s scope;
            # if not available, skip this guard (stay safe, never error).
            d_local <- get0("d", inherits = TRUE, ifnotfound = NULL)
            
            if (is.character(d_local) && length(d_local) == 1L) {
              used_day <- {
                asg <- get0("assignments", inherits = TRUE, ifnotfound = NULL)
                u <- 0L
                if (is.list(asg) && !is.null(asg[[d_local]])) {
                  df_asg <- asg[[d_local]]
                  if (is.data.frame(df_asg) && nrow(df_asg)) {
                    u <- as.integer(sum(as.integer(df_asg$`Assigned Surveys` %||% 0L), na.rm = TRUE))
                  }
                }
                u
              }
              # Default per-day floor for Months 1–2
              min_i <- 30L
              if (used_day < min_i) return(FALSE)
            }
          }
          
          tg <- get_targets()
          B <- as.numeric(controls$ampm_nudge %||% 7000.0)
          # Weekend band — enforce only when 'split' is ON
          if (isTRUE(tg$split)) {
            we_t <- tg$weekend / 100
            cur_we <- as.integer(cnt$tot_we %||% 0L)
            we_n  <- cur_we + if (is_we) k else 0L
            low_we <- (we_t - 0.10); high_we <- (we_t + 0.10)
            if (is_we  && (we_n / tot_n) > high_we) return(TRUE)
            if (!is_we && (we_n / tot_n) < low_we)  return(TRUE)
          }
          
          # AM band
          if (!tg$split) {
            am_t <- (tg$am_global / 100)
            cur_am <- as.integer(cnt$am %||% 0L)
            am_n <- cur_am + if (is_am) k else 0L
            if ((am_n / tot_n) > (am_t + 0.10) && is_am)  return(TRUE)
            if ((am_n / tot_n) < (am_t - 0.10) && !is_am) return(TRUE)
          } else {
            if (is_we) {
              tot0 <- as.integer(cnt$tot_we %||% 0L); am0 <- as.integer(cnt$am_we %||% 0L)
              tot_n2 <- tot0 + k; am_n2 <- am0 + if (is_am) k else 0L
              am_t <- (tg$am_we / 100)
              if (tot_n2 > 0) {
                if ((am_n2 / tot_n2) > (am_t + 0.10) && is_am)  return(TRUE)
                if ((am_n2 / tot_n2) < (am_t - 0.10) && !is_am) return(TRUE)
              }
            } else {
              tot0 <- as.integer(cnt$tot_wd %||% 0L); am0 <- as.integer(cnt$am_wd %||% 0L)
              tot_n2 <- tot0 + k; am_n2 <- am0 + if (is_am) k else 0L
              am_t <- (tg$am_wd / 100)
              if (tot_n2 > 0) {
                if ((am_n2 / tot_n2) > (am_t + 0.10) && is_am)  return(TRUE)
                if ((am_n2 / tot_n2) < (am_t - 0.10) && !is_am) return(TRUE)
              }
            }
          }
          FALSE
        }
        
        # How many more surveys can be added for this candidate without breaking bands
        band_room_for <- function(is_we, is_am) {
          cnt <- global_am_pm_counts()
          tot <- as.integer(cnt$tot %||% 0L)
          if (tot < band_threshold) return(1e9L)
          tg <- get_targets()
          # AM room
          if (!tg$split) {
            cur_am <- as.integer(cnt$am %||% 0L)
            low_am <- (tg$am_global/100 - 0.10)
            high_am<- (tg$am_global/100 + 0.10)
            if (is_am) {
              num <- high_am*tot - cur_am; den <- 1 - high_am
              room_am <- if (den > 0) floor(max(0, num/den)) else 0L
            } else {
              room_am <- if (low_am > 0) floor(max(0, (cur_am/low_am) - tot)) else 1e9L
            }
          } else if (is_we) {
            tot0 <- as.integer(cnt$tot_we %||% 0L); am0 <- as.integer(cnt$am_we %||% 0L)
            low_am <- (tg$am_we/100 - 0.10); high_am <- (tg$am_we/100 + 0.10)
            if (is_am) {
              num <- high_am*tot0 - am0; den <- 1 - high_am
              room_am <- if (den > 0) floor(max(0, num/den)) else 0L
            } else {
              room_am <- if (low_am > 0) floor(max(0, (am0/low_am) - tot0)) else 1e9L
            }
          } else {
            tot0 <- as.integer(cnt$tot_wd %||% 0L); am0 <- as.integer(cnt$am_wd %||% 0L)
            low_am <- (tg$am_wd/100 - 0.10); high_am <- (tg$am_wd/100 + 0.10)
            if (is_am) {
              num <- high_am*tot0 - am0; den <- 1 - high_am
              room_am <- if (den > 0) floor(max(0, num/den)) else 0L
            } else {
              room_am <- if (low_am > 0) floor(max(0, (am0/low_am) - tot0)) else 1e9L
            }
          }
          
          as.integer(max(0, room_am))
        }
        
        # ---- Per-day anchor dates (guarantee ≥1 realizable date per slot; choose max-coverage) ----
        # If "Specify which dates..." is OFF, choose—for each weekday—the date that maximizes route coverage,
        # sampling among the top 3 to keep diversity across tries. If it's ON, anchor to the first selected date.
        anchor_dates <- setNames(vector("list", length(days)), days)
        if (!isTRUE(input$restrict_dates_master)) {
          for (d in days) {
            df_d_all <- df %>% dplyr::filter(Day == d)
            if (nrow(df_d_all)) {
              cov <- df_d_all %>% dplyr::count(dep_date, name = "n") %>% dplyr::arrange(dplyr::desc(n))
              top_k <- min(3L, nrow(cov))
              pick  <- sample(seq_len(top_k), 1)
              anchor_dates[[d]] <- as.Date(cov$dep_date[pick])
            } else {
              anchor_dates[[d]] <- NULL
            }
          }
        } else {
          for (d in days) {
            sel <- allowed_dates_for(d)
            anchor_dates[[d]] <- if (!is.null(sel) && length(sel)) as.Date(sel[[1]]) else NULL
          }
        }
        if (is.finite(as.integer(state$debug_urn %||% NA_integer_))) {
          trace_urn <- as.integer(state$debug_urn %||% NA_integer_)
          for (d in days) {
            ad <- anchor_dates[[d]]
            df_d_all <- df %>% dplyr::filter(Day == d)
            has_any <- FALSE
            has_on_anchor <- FALSE
            if (is.data.frame(df_d_all) && nrow(df_d_all)) {
              urnv <- suppressWarnings(as.integer(df_d_all$`Unique Route Number`))
              has_any <- any(is.finite(urnv) & urnv == trace_urn, na.rm = TRUE)
              if (!is.null(ad)) {
                has_on_anchor <- any(
                  is.finite(urnv) & urnv == trace_urn &
                    as.Date(df_d_all$dep_date) == as.Date(ad),
                  na.rm = TRUE
                )
              }
            }
            debug_note(
              d, NA, "anchor_trace",
              list(
                trace_urn             = trace_urn,
                anchor_date           = as.character(if (!is.null(ad)) as.Date(ad) else NA),
                trace_has_any_flights = as.integer(if (isTRUE(has_any)) 1L else 0L),
                trace_on_anchor_date  = as.integer(if (isTRUE(has_on_anchor)) 1L else 0L)
              )
            )
          }
        }
        effective_dates_for <- function(d){
          if (isTRUE(input$restrict_dates_master)) return(allowed_dates_for(d))    # use exact UI dates
          ad <- anchor_dates[[d]]
          if (is.null(ad)) NULL else as.Date(ad)                                   # anchor date (scalar)
        }
        # ---- End per-day anchor dates ----
        
        day_cands <- vector("list", length(days))
        used_idx  <- vector("list", length(days))
        
        # Per-slot day caps (index by slot, not by day name) for planning
        day_caps_by_index <- sapply(seq_along(days), function(i) as.integer(day_caps[[days[i]]] %||% 40L))
        
        # --- NEW: pre-plan different windows for duplicate weekdays when hard-hours is ON ---
        slot_windows <- vector("list", length(days))
        dup_labels <- unique(days[duplicated(days)])
        for (lbl in dup_labels) {
          idxs_hard <- which(days == lbl & as.logical(hard_hours_flags))
          if (length(idxs_hard) >= 2) {
            eff_lbl <- effective_dates_for(lbl)
            pw <- plan_multi_windows_for_day(
              df_all = df,
              day_label = lbl,
              slot_indices = idxs_hard,
              eff_dates = eff_lbl,
              route_remaining = route_remaining_local,
              day_caps_by_index = day_caps_by_index,
              hours_caps = day_hours_caps,
              controls = controls,
              month = month,
              bin_caps = bin_caps,
              assigned_bins = if (month==3) live_bins_loc else NULL,
              latest_cap = latest_cap,
              hard_latest = hard_latest_applies
            )
            if (length(pw)) {
              for (nm in names(pw)) {
                idx <- suppressWarnings(as.integer(nm))
                if (is.finite(idx) && idx >= 1L && idx <= length(slot_windows) && length(pw[[nm]])) {
                  slot_windows[[idx]] <- pw[[nm]]
                }
              }
            }
          }
        }
        state$slot_windows <- slot_windows
        
        for (i in seq_along(days)) {
          d <- days[i]
          eff <- effective_dates_for(d)
          df_d <- df %>% dplyr::filter(Day == d, if (!is.null(eff)) dep_date %in% eff else TRUE)
          if (!nrow(df_d)) { day_cands[[i]] <- df_d[0,]; used_idx[[i]] <- logical(0); next }
          
          # If this slot got a planned window (duplicate weekday case), use it.
          # Otherwise (single occurrence + hard-hours), optionally pick a best window just for this slot.
          win_bounds <- if (i <= length(slot_windows)) slot_windows[[i]] else NULL
          if (is.null(win_bounds) && isTRUE(hard_hours_flags[i]) && sum(days == d) == 1L) {
            win_bounds <- best_time_window(
              df_day = df_d,
              route_remaining = route_remaining_local,
              day_cap = as.integer(day_caps[[d]] %||% 40L),
              hours_cap = day_hours_caps[i],
              controls = controls,
              month = month,
              bin_caps = bin_caps,
              already_assigned_bins = if (month==3) live_bins_loc else NULL,
              day_name = d
            )
          }
          
          cand <- df_d %>%
            dplyr::mutate(
              DepMin = vapply(`Departure Time`, parse_user_time, integer(1)),
              DepMin = ((DepMin %% 1440) + 1440) %% 1440,
              AM = is.finite(DepMin) & DepMin < 12*60,
              PM = is.finite(DepMin) & DepMin >= 12*60
            ) %>%
            dplyr::filter(is.finite(DepMin))
          
          if (is.finite(latest_cap) && hard_latest_applies) cand <- cand %>% dplyr::filter(DepMin <= latest_cap)
          if (!is.null(win_bounds)) {
            wmin <- as.integer(win_bounds$start %||% NA_integer_)
            cap_hours_i <- as.integer(pmax(1L, nzint(day_hours_caps[i] %||% controls$max_hours %||% 6L)))
            if (is.finite(wmin) && is.finite(cap_hours_i)) {
              # Full-span window from the chosen start; respect hard latest if enabled
              wmax <- wmin + cap_hours_i * 60L
              if (is.finite(latest_cap) && hard_latest_applies) wmax <- min(wmax, as.integer(latest_cap))
            } else {
              # Fallback to provided end if start/cap are not finite
              wmax <- as.integer(win_bounds$end %||% NA_integer_)
            }
            # Apply the planned window only when Hard Hours = ON for this slot (any month),
            # and bias it toward PM if the AM ledger is already heavy; never apply if it would be empty.
            hard_hours_now <- tryCatch(isTRUE(state$hard_hours_flags[[i]]), error = function(e) FALSE)
            if (isTRUE(hard_hours_now) && is.finite(wmin) && is.finite(wmax)) {
              # Compute side preference from AM/PM ledger (same logic as later)
              prefer_side <- NULL
              if (month %in% c(1L,2L) && exists("ampm_left", inherits = TRUE)) {
                if (isTRUE(am_controls$split)) {
                  if (is_weekend(d)) {
                    diff_lr <- as.integer((ampm_left$PM_we %||% 0L) - (ampm_left$AM_we %||% 0L))
                  } else {
                    diff_lr <- as.integer((ampm_left$PM_wk %||% 0L) - (ampm_left$AM_wk %||% 0L))
                  }
                } else {
                  diff_lr <- as.integer((ampm_left$PM %||% 0L) - (ampm_left$AM %||% 0L))
                }
                if (diff_lr >= 1L) prefer_side <- "PM"
                if (diff_lr <= -1L) prefer_side <- "AM"
              }
              # If PM is preferred and the window starts before noon, shift the window to the PM side
              if (identical(prefer_side, "PM") && is.finite(cap_hours_i) && wmin < 12L*60L) {
                wmin <- max(12L*60L, wmin)
                wmax <- wmin + cap_hours_i * 60L
                if (is.finite(latest_cap) && hard_latest_applies) wmax <- min(wmax, as.integer(latest_cap))
              }
              # NOTE: Planned window is now a SOFT preference only (scoring bonus).
              # Max-hours is enforced later using the rolling earliest↔latest span rule.
            }
          }
          # Persist a window for this slot so later passes (and diagnostics) can clamp by it
          if (is.null(slot_windows)) slot_windows <- vector("list", length(days))
          if (is.null(slot_windows[[i]]) && !is.null(win_bounds)) slot_windows[[i]] <- win_bounds
          cand <- cand %>% dplyr::left_join(route_freq, by="Unique Route Number")
          cand$freq[is.na(cand$freq)] <- 0L
          
          day_cands[[i]] <- cand
          used_idx[[i]]  <- rep(FALSE, nrow(cand))
          # Debug: record day-level candidate counts before & after time filters
          cand_pre <- df_d %>%
            dplyr::mutate(
              DepMin = vapply(`Departure Time`, parse_user_time, integer(1)),
              DepMin = ((DepMin %% 1440) + 1440) %% 1440
            ) %>%
            dplyr::filter(is.finite(DepMin))
          
          pre_n <- nrow(cand_pre)
          drop_latest <- if (is.finite(latest_cap) && hard_latest_applies) sum(cand_pre$DepMin > latest_cap) else 0L
          
          if (!is.null(win_bounds)) {
            wmin_dbg <- as.integer(win_bounds$start %||% NA_integer_)
            cap_hours_i <- as.integer(pmax(1L, nzint(day_hours_caps[i] %||% controls$max_hours %||% 6L)))
            wmax_dbg <- if (is.finite(wmin_dbg) && is.finite(cap_hours_i)) {
              wmin_dbg + cap_hours_i * 60L
            } else {
              as.integer(win_bounds$end %||% NA_integer_)
            }
            if (is.finite(wmax_dbg) && is.finite(wmin_dbg) && is.finite(latest_cap) && hard_latest_applies)
              wmax_dbg <- min(wmax_dbg, as.integer(latest_cap))
            drop_window <- if (is.finite(wmin_dbg) && is.finite(wmax_dbg))
              sum(!(cand_pre$DepMin >= wmin_dbg & cand_pre$DepMin <= wmax_dbg)) else 0L
          } else {
            drop_window <- 0L
          }
          
          debug_note(d, i, "day_cands",
                     list(
                       pre = pre_n,
                       after_latest = pre_n - drop_latest,
                       after_window = pre_n - drop_window,
                       final = nrow(cand)
                     ))
        }
        
        state$slot_windows <- slot_windows
        assigned_day <- setNames(rep(0L, length(days)), days)
        cap_left     <- setNames(as.integer(day_caps), days)
        
        # Keep your min_per_day from earlier (Month 3 + fine-tune)
        min_left     <- setNames(as.integer(min_per_day %||% 0L), days)
        
        # FIX: keep per-slot state indexed by i (no names)
        last_time  <- rep(-Inf, length(days))  # last picked DepMin (for spacing checks)
        first_time <- rep( Inf, length(days))  # earliest DepMin placed on this slot
        max_time   <- rep(-Inf, length(days))  # latest  DepMin placed on this slot (true max)
        # Track earliest concourse and time of last concourse change (Months 1–2 logic)
        first_conc       <- rep(NA_character_, length(days))
        last_change_time <- rep(NA_real_,      length(days))
        last_conc  <- rep(NA_character_, length(days))
        last_S     <- rep(0L,   length(days))
        end_time_comp <- rep(-Inf, length(days))  # latest completion time (dep + tail) for objective span
        bin_room_remaining <- function(bin_name) {
          if (is.null(bin_caps) || is.null(bin_caps[[bin_name]]) || !is.finite(as.numeric(bin_caps[[bin_name]]))) return(1e9L)
          cap <- as.integer(bin_caps[[bin_name]] %||% 0L)
          used <- as.integer(live_bins_loc[[bin_name]] %||% 0L)
          pmax(0L, cap - used)
        }
        
        w_rem    <- if (month == 3) 50.0 else 10.0
        w_intl   <- if (isTRUE(controls$prior_intl)) 5000.0 else 0.0
        w_infreq <- if (isTRUE(controls$prior_infreq)) (if (month==3) 100.0 else 2500.0) else 0.0
        w_switch <- if (month == 3) 0.5 else 5.0
        w_bin    <- 0.0
        w_compact <- if (month == 3) -0.1 else 0.05
        w_spread_if_violate <- 0.15   # Month 3: reward increasing span ONLY when spacing would otherwise be violated
        w_scarce0 <- 250.0   # URN has 0 alternate eligible slots -> must-place
        w_scarce1 <- 80.0   # URN has 1 alternate eligible slot  -> very tight
        w_scarcity_m12 <- if (month==3) 0.0 else 100.0   # Month 1–2 whole-month scarcity weight (unified to Month 1)
        
        max_rem  <- max(route_remaining_local$remaining %||% 0L, na.rm=TRUE); if (!is.finite(max_rem) || max_rem<=0) max_rem <- 1
        stall_scans <- 0L
        rr_toggle <- 0L  # soft round-robin toggle: odd=pick from most underfilled day, even=global best
        
        repeat {
          did_commit <- FALSE
          need_min <- names(which(min_left > 0L))
          candidate_i <- which(cap_left > 0L & vapply(seq_along(days), function(i) { if (length(need_min)) days[i] %in% need_min else TRUE }, logical(1)))
          # Soft round-robin: on odd toggles, restrict to the most underfilled day(s)
          if ((rr_toggle %% 2L) == 1L && length(candidate_i) > 1L) {
            left_vec <- vapply(candidate_i, function(ii) as.integer(cap_left[[ days[ii] ]] %||% 0L), integer(1))
            # Only consider days that have any unused candidates in their per-day pool right now
            pool_ok <- vapply(candidate_i, function(ii) {
              ci <- day_cands[[ii]]
              if (!is.data.frame(ci) || !nrow(ci)) return(FALSE)
              any(!used_idx[[ii]])
            }, logical(1))
            if (any(pool_ok)) {
              candidate_i <- candidate_i[pool_ok]
              left_vec    <- left_vec[pool_ok]
              mx <- max(left_vec, na.rm = TRUE)
              keep_idx <- candidate_i[which(left_vec == mx)]
              candidate_i <- keep_idx
              debug_note("ALL", NA, "rr_underfill_pass",
                         list(days = paste(days[candidate_i], collapse=","), cap_left = paste(left_vec[left_vec == mx], collapse=",")))
            } else {
              debug_note("ALL", NA, "round_robin_skipped_no_pool", list())
            }
          }
          rr_toggle <- rr_toggle + 1L
          
          if (!length(candidate_i)) break
          if (jitter_sd > 0) candidate_i <- sample(candidate_i)  # randomize slot scan order
          debug_note("ALL", NA, "iter_scan",
                     list(
                       cands        = as.integer(length(candidate_i)),
                       cap_left_csv = paste0(as.integer(cap_left), collapse = ",")
                     ))
          
          # >>> NEW: ledger-guided day ordering (Months 1–2) <<<
          if (month %in% c(1,2) && length(candidate_i) > 1L) {
            cnt <- global_am_pm_counts()
            tg  <- get_targets()
            pm_short <- FALSE; am_short <- FALSE
            if (!isTRUE(tg$split)) {
              am_t <- (as.numeric(tg$am_global %||% 45)) / 100
              tot0 <- as.integer(cnt$tot %||% 0L); am0 <- as.integer(cnt$am %||% 0L)
              cur  <- if (tot0 > 0L) am0 / tot0 else am_t
              pm_short <- (cur > (am_t + 0.05))
              am_short <- (cur < (am_t - 0.05))
            } else {
              # Use the overall ledger signal for simplicity
              am_t <- (as.numeric((cnt$tot_we %||% 0L) + (cnt$tot_wd %||% 0L)) > 0L) # dummy to keep structure
              am_t <- (as.numeric(tg$am_global %||% 45)) / 100
              tot0 <- as.integer(cnt$tot %||% 0L); am0 <- as.integer(cnt$am %||% 0L)
              cur  <- if (tot0 > 0L) am0 / tot0 else am_t
              pm_short <- (cur > (am_t + 0.05))
              am_short <- (cur < (am_t - 0.05))
            }
            if (pm_short || am_short) {
              med_dep <- vapply(candidate_i, function(ii){
                v <- as.integer(day_cands[[ii]]$DepMin)
                if (!length(v) || all(!is.finite(v))) return(NA_real_)
                stats::median(v, na.rm = TRUE)
              }, numeric(1))
              ord <- if (pm_short) order(med_dep, decreasing = TRUE, na.last = TRUE)
              else          order(med_dep, decreasing = FALSE, na.last = TRUE)
              candidate_i <- candidate_i[ord]
              debug_note("ALL", NA, "iter_day_order",
                         list(pm_short = isTRUE(pm_short),
                              am_short = isTRUE(am_short),
                              order_names = paste0(days[candidate_i], collapse=",")))
            }
          }
          
          best <- NULL; best_score <- -Inf
          
          for (i in candidate_i) {
            d <- days[i]
            cand <- day_cands[[i]]
            if (!nrow(cand)) next
            
            pool <- cand[!used_idx[[i]], , drop = FALSE]
            debug_note(
              d, i, "slot_pool_start",
              c(
                list(pool_n = nrow(pool)),
                debug_trace_pool(pool)
              )
            )
            if (!nrow(pool)) next
            
            pool <- pool %>%
              dplyr::left_join(route_remaining_local %>%
                                 dplyr::select(`Unique Route Number`, remaining),
                               by = "Unique Route Number")
            pool$remaining[is.na(pool$remaining)] <- 0L
            raw_cap <- pmin(pmax(0L, pool$remaining), per_f_cap)
            
            if (month == 3 && !is.null(bin_caps)) {
              pool$bin <- mapply(flight_bin, pool$Day, pool$DepMin)
              pool$bin_room <- vapply(pool$bin, function(b) if (is.na(b)) 0L else bin_room_remaining(b), integer(1))
              has_room <- pool$bin_room > 0L
              if (!any(has_room)) next
              pool <- pool[has_room, , drop = FALSE]
              raw_cap <- as.integer(raw_cap[has_room])
            } else {
              pool$bin <- NA_character_
              pool$bin_room <- Inf
            }
            
            feas <- which(raw_cap > 0L)
            debug_note(
              d, i, "slot_pool_feasible",
              c(
                list(
                  feasible_n    = as.integer(length(feas)),
                  zero_remaining = as.integer(sum(raw_cap <= 0))
                ),
                debug_trace_pool(pool)
              )
            )
            if (!length(feas)) next
            pool <- pool[feas, , drop = FALSE]
            raw_cap <- as.integer(raw_cap[feas])
            # --- Approach A: if the weekly ledger is short on one side, allow a pure side window ---
            prefer_side <- NULL
            if (month %in% c(1L, 2L)) {
              # Decide which ledger to consult (split vs. unified)
              if (isTRUE(am_controls$split)) {
                if (isTRUE(is_weekend(d))) {
                  diff_lr <- as.integer((ampm_left$PM_we %||% 0L) - (ampm_left$AM_we %||% 0L))
                } else {
                  diff_lr <- as.integer((ampm_left$PM_wk %||% 0L) - (ampm_left$AM_wk %||% 0L))
                }
              } else {
                diff_lr <- as.integer((ampm_left$PM %||% 0L) - (ampm_left$AM %||% 0L))
              }
              if (diff_lr >= 1L) prefer_side <- "PM"
              if (diff_lr <= -1L) prefer_side <- "AM"
            }
            
            if (!is.null(prefer_side)) {
              debug_note(d, i, "slot_prefer_side_soft",
                         list(
                           prefer = as.character(prefer_side),
                           pool_n = as.integer(nrow(pool))
                         ))
            }
            
            # ---- Rolling max-hours window (Months 1–2) ----
            if (month %in% c(1,2)) {
              H_min <- as.integer(pmax(1L, nzint(day_hours_caps[i] %||% controls$max_hours %||% 6L)) * 60L)
              ft_i <- as.integer(first_time[i]); lt_i <- as.integer(max_time[i])
              allow_min <- if (is.finite(lt_i)) (lt_i - H_min) else -Inf
              allow_max <- if (is.finite(ft_i)) (ft_i + H_min) else  Inf
              
              # NEW: log rolling-window bounds and pre/post counts
              debug_note(d, i, "slot_window",
                         list(
                           H_min      = as.integer(H_min),
                           first_time = as.integer(ifelse(is.finite(ft_i), ft_i, -1L)),
                           max_time   = as.integer(ifelse(is.finite(lt_i), lt_i, -1L)),
                           allow_min  = as.integer(ifelse(is.finite(allow_min), allow_min, -1L)),
                           allow_max  = as.integer(ifelse(is.finite(allow_max), allow_max, -1L)),
                           pool_n_before = as.integer(nrow(pool))
                         ))
              
              keep_idx <- which(is.finite(as.integer(pool$DepMin)) &
                                  (as.integer(pool$DepMin) >= allow_min) &
                                  (as.integer(pool$DepMin) <= allow_max))
              # NOTE: Sentinel union removed. Pool should contain ONLY flights that are feasible
              # under the rolling max-hours band; we do not retain out-of-band anchors.
              
              # NEW: record survivors and drop count
              trace_fields <- list()
              urn_trace <- as.integer(state$debug_urn %||% NA_integer_)
              if (is.finite(urn_trace) && "Unique Route Number" %in% names(pool)) {
                urnv <- suppressWarnings(as.integer(pool$`Unique Route Number`))
                in_before <- any(is.finite(urnv) & urnv == urn_trace, na.rm = TRUE)
                in_after  <- if (length(keep_idx)) {
                  any(is.finite(urnv[keep_idx]) & urnv[keep_idx] == urn_trace, na.rm = TRUE)
                } else {
                  FALSE
                }
                trace_fields <- list(
                  trace_urn       = urn_trace,
                  trace_in_before = as.integer(if (isTRUE(in_before)) 1L else 0L),
                  trace_in_after  = as.integer(if (isTRUE(in_after)) 1L else 0L)
                )
              }
              
              debug_note(
                d, i, "slot_after_window_filter",
                c(
                  list(
                    kept    = as.integer(length(keep_idx)),
                    dropped = as.integer(nrow(pool) - length(keep_idx))
                  ),
                  trace_fields
                )
              )
              # Replace simple 'next' with logged exit
              if (length(keep_idx) == 0L) {
                debug_note(d, i, "slot_window_empty",
                           list(
                             H_min      = as.integer(H_min),
                             allow_min  = as.integer(ifelse(is.finite(allow_min), allow_min, -1L)),
                             allow_max  = as.integer(ifelse(is.finite(allow_max), allow_max, -1L))
                           ))
                next
              }
              
              # >>> NEW: clamp earliest possible *start* when Hard Earliest is ON <<<
              if (isTRUE(hard_hours_flags[i]) && is.finite(earliest_cap)) {
                earliest_start_allowed <- as.integer(earliest_cap)
                
                debug_note(d, i, "slot_earliest_start_clamp",
                           list(
                             earliest_cap            = as.integer(earliest_cap),
                             earliest_start_allowed  = as.integer(earliest_start_allowed),
                             pre_clamp_kept          = as.integer(length(keep_idx))
                           ))
                
                keep_idx <- keep_idx[ as.integer(pool$DepMin[keep_idx]) >= earliest_start_allowed ]
                
                debug_note(d, i, "slot_after_earliest_start",
                           list(
                             kept_after_earliest   = as.integer(length(keep_idx))
                           ))
                
                if (length(keep_idx) == 0L) {
                  debug_note(d, i, "slot_earliest_start_empty",
                             list(
                               earliest_cap           = as.integer(earliest_cap),
                               earliest_start_allowed = as.integer(earliest_start_allowed)
                             ))
                  # bump stall counter for this day
                  state$stall_counts <- { x <- (state$stall_counts %||% rep(0L, length(days))); x[i] <- x[i] + 1L; x }
                  next
                }
              }
              
              # >>> NEW: half-day guard for first picks on a day (Months 1–2) <<<
              if (month %in% c(1,2)) {
                assigned_so_far_local <- as.integer(assigned_day[[d]] %||% 0L)
                if (assigned_so_far_local < 8L && length(keep_idx) > 0L) {
                  cnt <- global_am_pm_counts()
                  tg  <- get_targets()
                  need_pm <- FALSE; need_am <- FALSE
                  if (!isTRUE(tg$split)) {
                    am_t <- (as.numeric(tg$am_global %||% 45)) / 100
                    tot0 <- as.integer(cnt$tot %||% 0L); am0 <- as.integer(cnt$am %||% 0L)
                    cur  <- if (tot0 > 0L) am0 / tot0 else am_t
                    need_pm <- (cur > (am_t + 0.05))
                    need_am <- (cur < (am_t - 0.05))
                  } else {
                    if (is_weekend(d)) {
                      am_t <- (as.numeric(tg$am_we %||% 45)) / 100
                      tot0 <- as.integer(cnt$tot_we %||% 0L); am0 <- as.integer(cnt$am_we %||% 0L)
                    } else {
                      am_t <- (as.numeric(tg$am_wd %||% 45)) / 100
                      tot0 <- as.integer(cnt$tot_wd %||% 0L); am0 <- as.integer(cnt$am_wd %||% 0L)
                    }
                    cur  <- if (tot0 > 0L) am0 / tot0 else am_t
                    need_pm <- (cur > (am_t + 0.05))
                    need_am <- (cur < (am_t - 0.05))
                  }
                  pre_guard <- length(keep_idx)
                  if (isTRUE(need_pm)) {
                    keep_idx <- keep_idx[ as.integer(pool$DepMin[keep_idx]) >= (12L*60L) ]
                  } else if (isTRUE(need_am)) {
                    keep_idx <- keep_idx[ as.integer(pool$DepMin[keep_idx]) <  (12L*60L) ]
                  }
                  debug_note(d, i, "slot_half_day_guard",
                             list(need_pm = isTRUE(need_pm),
                                  need_am = isTRUE(need_am),
                                  kept_before = as.integer(pre_guard),
                                  kept_after  = as.integer(length(keep_idx))))
                }
              }
              
              pool <- pool[keep_idx, , drop = FALSE]
              raw_cap <- as.integer(raw_cap[keep_idx])
              debug_note(d, i, "slot_pool_after_window_apply",
                         list(pool_n = as.integer(nrow(pool))))
              # NOTE (2025-12): "recenter" fallback removed.
              # We now keep first_time/max_time as TRUE earliest/latest scheduled times
              # and enforce max-hours only via the rolling earliest↔latest span feasibility band.
              if (isTRUE(((state$stall_counts %||% rep(0L, length(days)))[i] >= 6L))) {
                debug_note(d, i, "slot_recenter_disabled",
                           list(
                             stalled = 1L,
                             assigned_so_far = as.integer(sum((assignments[[i]]$`Assigned Surveys`) %||% 0L, na.rm = TRUE))
                           ))
              }
              
              # >>> NEW: drop already-scheduled for this day (by URN + DepMin) <<<
              if (is.data.frame(assignments[[i]]) && nrow(assignments[[i]]) && nrow(pool)) {
                used_keys <- paste0(as.integer(assignments[[i]]$`Unique Route Number`), "_", as.integer(assignments[[i]]$DepMin))
                pool_keys <- paste0(as.integer(pool$`Unique Route Number`), "_", as.integer(pool$DepMin))
                keep2 <- !(pool_keys %in% used_keys)
                if (!all(keep2)) {
                  pool    <- pool[keep2, , drop = FALSE]
                  raw_cap <- as.integer(raw_cap[keep2])
                  debug_note(d, i, "slot_drop_already_scheduled",
                             list(dropped = as.integer(sum(!keep2)), kept = as.integer(sum(keep2))))
                }
              }
              # <<< END NEW >>>
            }
            
            # --- per-slot state (index i) ---
            pool$ConcourseClean <- cclean(pool$Concourse)
            prev_conc       <- last_conc[i]
            last_conc_clean <- if (is.null(prev_conc) || is.na(prev_conc)) NA_character_ else cclean(prev_conc)
            conc_change     <- ifelse(is.na(last_conc_clean), FALSE, pool$ConcourseClean != last_conc_clean)
            
            # Keep these for other scoring penalties (switch_pen etc.), but NOT for feasibility
            prev_last_time  <- last_time[i]
            prev_first_time <- first_time[i]
            prev_max_time   <- max_time[i]
            prev_S          <- last_S[i]
            
            # ---- Bilateral interflight spacing feasibility (does NOT assume append-only) ----
            # Month 1–2: always hard-enforce spacing. Month 3: enforce only when the checkbox is ON.
            if (isTRUE(month %in% c(1L, 2L) || isTRUE(input$enforce_spacing))) {
              # Aggregate scheduled flights for this slot by DepMin
              dep_sched <- integer(0); conc_sched <- character(0); Sv_sched <- integer(0)
              if (is.data.frame(assignments[[i]]) && nrow(assignments[[i]])) {
                si <- assignments[[i]]
                depv <- suppressWarnings(as.integer(si$DepMin))
                okv <- is.finite(depv)
                if (any(okv)) {
                  si <- si[okv, , drop = FALSE]
                  depv <- as.integer(si$DepMin)
                  ord <- order(depv)
                  si <- si[ord, , drop = FALSE]
                  depv <- depv[ord]
                  
                  Sv <- as.integer(si$`Assigned Surveys` %||% 0L)
                  Sv[is.na(Sv)] <- 0L
                  concv <- cclean(si$Concourse)
                  
                  udep <- unique(depv)
                  Sv_sched <- vapply(udep, function(t) sum(Sv[depv == t], na.rm = TRUE), integer(1))
                  conc_sched <- vapply(udep, function(t) concv[which(depv == t)[1L]], character(1))
                  dep_sched <- as.integer(udep)
                }
              }
              
              # Candidate spacing feasibility mask + cap based on next-gap
              spacing_ok <- rep(TRUE, nrow(pool))
              maxS_next  <- rep(1000000000L, nrow(pool))
              blocked_prev <- 0L
              blocked_next <- 0L
              
              if (length(dep_sched) && nrow(pool)) {
                cand_dep <- as.integer(pool$DepMin)
                pos <- findInterval(cand_dep, dep_sched)
                
                # Prev neighbor constraint: cand_dep >= prev_dep + spacing_after(prev_S, conc_change)
                has_prev <- pos >= 1L
                if (any(has_prev)) {
                  prev_dep <- dep_sched[pos[has_prev]]
                  prev_Sv  <- Sv_sched[pos[has_prev]]
                  prev_cc  <- conc_sched[pos[has_prev]]
                  
                  need_prev <- mapply(function(sv, cc_prev, cc_cand) {
                    spacing_after(as.integer(sv), concourse_change = !identical(cclean(cc_prev), cclean(cc_cand)))
                  }, prev_Sv, prev_cc, pool$ConcourseClean[has_prev])
                  
                  spacing_ok[has_prev] <- cand_dep[has_prev] >= (as.integer(prev_dep) + as.integer(need_prev))
                  blocked_prev <- as.integer(sum(has_prev & !spacing_ok, na.rm = TRUE))
                }
                
                # Next neighbor constraint becomes a cap on how many surveys this candidate can take
                has_next <- pos < length(dep_sched)
                if (any(has_next)) {
                  next_dep <- dep_sched[pos[has_next] + 1L]
                  next_cc  <- conc_sched[pos[has_next] + 1L]
                  
                  gap_next <- as.integer(next_dep) - cand_dep[has_next]
                  cc_cand_next <- pool$ConcourseClean[has_next]
                  cc_cand_next[is.na(cc_cand_next)] <- ""
                  next_cc_clean <- cclean(next_cc)
                  next_cc_clean[is.na(next_cc_clean)] <- ""
                  extra <- ifelse(cc_cand_next != next_cc_clean, 15L, 0L)
                  
                  avail <- gap_next - as.integer(extra)
                  avail[!is.finite(avail)] <- -1L
                  avail[avail < 0L] <- -1L
                  
                  k <- floor(avail / 10L)
                  k[!is.finite(k)] <- -1L
                  k[k < 0L] <- -1L
                  
                  maxS_next[has_next] <- pmax(0L, as.integer(2L * k))
                  blocked_next <- as.integer(sum(has_next & (maxS_next[has_next] < 1L), na.rm = TRUE))
                }
              }
              
              # Apply next-gap cap to row caps and drop anything that cannot take >= 1 survey
              raw_cap <- as.integer(pmin(as.integer(raw_cap), as.integer(maxS_next)))
              spacing_ok <- spacing_ok & (raw_cap >= 1L)
              
              debug_note(d, i, "spacing_bilateral",
                         c(
                           list(
                             pool_n        = as.integer(nrow(pool)),
                             sched_n       = as.integer(length(dep_sched)),
                             blocked_prev  = as.integer(blocked_prev),
                             blocked_next  = as.integer(blocked_next),
                             blocked_total = as.integer(sum(!spacing_ok, na.rm = TRUE))
                           ),
                           debug_trace_pool(pool)
                         ))
              
              if (any(!spacing_ok)) {
                keep_sp <- spacing_ok
                pool <- pool[keep_sp, , drop = FALSE]
                raw_cap <- as.integer(raw_cap[keep_sp])
                conc_change <- conc_change[keep_sp]
              }
            }
            # Spacing is now a hard feasibility rule in the pool, so these are no longer used as penalties
            spacing_ok <- rep(TRUE, nrow(pool))
            minutes_short <- rep(0.0, nrow(pool))
            new_first <- if (is.finite(prev_first_time)) pmin(prev_first_time, pool$DepMin) else pool$DepMin
            new_last  <- if (is.finite(prev_max_time))   pmax(prev_max_time,   pool$DepMin) else pool$DepMin
            span_new  <- as.numeric(new_last) - as.numeric(new_first)
            
            cap_hours <- day_hours_caps[i] %||% controls$max_hours %||% 6L
            max_span  <- pmax(1L, as.integer(cap_hours)) * 60L
            
            # Hard-hours candidate filter (vectorized)
            # Month 1–2: always enforce the max-hours span, regardless of checkbox,
            # to avoid later post-clamping that can underfill a day and desync diagnostics.
            if (isTRUE(month %in% c(1L, 2L) || hard_hours_flags[i]) && is.finite(max_span)) {
              would_exceed_hours <- (span_new > max_span)
              would_exceed_hours[is.na(would_exceed_hours)] <- FALSE
            } else {
              would_exceed_hours <- rep(FALSE, nrow(pool))
              debug_note(d, i, "slot_checks",
                         list(
                           pool_n = as.integer(nrow(pool)),
                           spacing_blocked = as.integer(sum(!spacing_ok, na.rm = TRUE)),
                           hardhours_blocked = as.integer(sum(would_exceed_hours, na.rm = TRUE))
                         ))
              
            }
            
            if (isTRUE(all(would_exceed_hours))) {
              urns_blocked <- unique(as.integer(pool$`Unique Route Number`[is.finite(pool$`Unique Route Number`)]))
              if (!length(bypass_acc_loc$hard_hours_blocked[[d]])) bypass_acc_loc$hard_hours_blocked[[d]] <- integer(0)
              bypass_acc_loc$hard_hours_blocked[[d]] <- unique(c(bypass_acc_loc$hard_hours_blocked[[d]], urns_blocked))
              debug_note(d, i, "slot_hardhours_all", list(hardhours_removed = as.integer(nrow(pool))))
              next
            }
            if (isTRUE(any(would_exceed_hours))) {
              keep <- !would_exceed_hours
              removed_n <- sum(!keep)
              pool <- pool[keep, , drop = FALSE]
              raw_cap <- raw_cap[keep]
              spacing_ok <- spacing_ok[keep]
              minutes_short <- minutes_short[keep]
              conc_change <- conc_change[keep]
              debug_note(d, i, "slot_after_hardhours",
                         list(
                           pool_n = as.integer(nrow(pool)),
                           hardhours_removed = as.integer(removed_n)
                         ))
              if (!nrow(pool)) next
            }
            pools_now <- current_bin_pools(d)
            bin_bonus <- ifelse(pool$AM & (pools_now$AM > 0), w_bin, 0) +
              ifelse(pool$PM & (pools_now$PM > 0), w_bin, 0)
            
            ft <- tolower(as.character(pool$`Flight Type` %||% ""))
            
            # Per-slot previous state for switching penalty
            switch_pen <- ifelse(
              is.na(prev_conc),
              0,
              ifelse(
                pool$Concourse != prev_conc &
                  is.finite(prev_last_time) &
                  (as.numeric(pool$DepMin) - as.numeric(prev_last_time) < 90),
                w_switch, 0
              )
            )
            rem_score    <- (pool$remaining / max_rem) * w_rem
            intl_bonus   <- ifelse(ft == "international", w_intl, 0)
            
            # Infrequent-by-frequency (all months; linear by days/week: 7→0, 2→high, 1→very high)
            infreq_bonus <- if (isTRUE(controls$prior_infreq)) {
              f <- pmax(1L, pmin(7L, as.integer(pool$freq %||% NA_integer_))); f[is.na(f)] <- 7L
              ((7L - f) / 6.0) * w_infreq
            } else 0.0
            
            # Spacing used strictly as a tie-breaker for Months 1–2; Month 3 unchanged
            if (month %in% c(1, 2)) {
              max_cap_now <- if (length(raw_cap)) as.integer(max(raw_cap, na.rm = TRUE)) else 0L
              in_tie      <- (as.integer(raw_cap) == max_cap_now)
              spacing_pen <- ifelse(in_tie & !spacing_ok, 4.0 + minutes_short/10, 0.0)
            } else {
              spacing_pen <- ifelse(spacing_ok, 0, 4.0 + minutes_short/10)
            }
            # --- Diagnostics: survivors after all filters + simple packability estimate for this slot ---
            kept_after_all_filters <- as.integer(nrow(pool) %||% 0L)
            # crude upper bound for this slot: sum of row caps, limited by the day capacity left
            cap_left_here <- as.integer((cap_left[[d]] %||% 0L))
            ub_slot <- 0L
            if (kept_after_all_filters > 0L) {
              # sum of feasible per-row caps based on remaining and per-flight cap
              ub_slot <- sum(as.integer(pmax(0L, pmin(as.integer(pool$remaining %||% 0L), as.integer(per_f_cap %||% 10L)))) %||% 0L, na.rm = TRUE)
            }
            pack_estimate <- as.integer(pmax(0L, pmin(cap_left_here, ub_slot)))
            debug_note(
              d, i, "slot_pool_final",
              c(
                list(
                  kept_after_all_filters = kept_after_all_filters,
                  pack_estimate          = pack_estimate
                ),
                debug_trace_pool(pool)
              )
            )
            # Incremental span for objective
            if (month %in% c(1,2)) {
              # completion-aware span (2 tablets; 10 minutes per 2 surveys; odd rounds up)
              tail_est <- as.numeric(10 * ceiling(raw_cap/2))
              cand_end <- if (is.finite(end_time_comp[i])) pmax(end_time_comp[i], as.numeric(pool$DepMin) + tail_est) else as.numeric(pool$DepMin) + tail_est
              prev_end_span <- if (is.finite(end_time_comp[i]) && is.finite(prev_first_time)) as.numeric(end_time_comp[i]) - as.numeric(prev_first_time) else 0
              new_end_span  <- if (is.finite(prev_first_time)) as.numeric(cand_end) - as.numeric(pmin(prev_first_time, pool$DepMin)) else 0
              inc_span <- pmax(0, new_end_span - prev_end_span)
            } else {
              inc_span <- ifelse(
                is.finite(prev_max_time) & is.finite(prev_first_time),
                (pmax(prev_max_time, pool$DepMin) - pmin(prev_first_time, pool$DepMin)) -
                  (as.numeric(prev_max_time) - as.numeric(prev_first_time)),
                0
              )
            }
            # Compactness / spread only helps when it reduces spacing violations:
            # - Month 3: if spacing is NOT ok, reward spreading out (negative "penalty" so it's added to score).
            # - Months 1–2: keep compactness penalty as before.
            span_pen <- if (month == 3) {
              ifelse(spacing_ok,
                     0,
                     - w_spread_if_violate * (pmax(0, as.numeric(inc_span)) / 10))
            } else {
              # Months 1–2: keep compactness OFF until day reaches its cap
              slot_used_i <- as.integer(assigned_day[[d]] %||% 0L)
              slot_cap_i  <- as.integer(day_caps[[d]] %||% 40L)
              ifelse(slot_used_i < slot_cap_i, 0, w_compact * (pmax(0, as.numeric(inc_span)) / 10))
            }
            # --- scarcity bonus
            
            # Months 1–2: moved into infrequent bonus; keep separate scarcity neutral.
            # Month 3: keep existing "alternate eligible slots" scarcity.
            if (month %in% c(1,2)) {
              scarcity_bonus <- rep(0.0, nrow(pool))
            } else {
              
              # Month 3 (current behavior): favor URNs with few alternate eligible slots
              alt_count <- integer(nrow(pool))
              other_slots <- setdiff(candidate_i, i)
              for (r in seq_len(nrow(pool))) {
                urnr <- as.integer(pool$`Unique Route Number`[r])
                cnt <- 0L
                for (j in other_slots) {
                  candj <- day_cands[[j]][!used_idx[[j]], , drop = FALSE]
                  if (!nrow(candj)) next
                  # Same route?
                  candj <- candj[candj$`Unique Route Number` == urnr, , drop = FALSE]
                  if (!nrow(candj)) next
                  # Respect remaining and per-flight cap
                  remj <- route_remaining_local$remaining[match(urnr, route_remaining_local$`Unique Route Number`)]
                  remj <- as.integer(remj %||% 0L)
                  row_cap_j <- pmin(pmax(0L, remj), per_f_cap)
                  if (row_cap_j <= 0L) next
                  # Respect bin caps
                  bj <- mapply(flight_bin, candj$Day, candj$DepMin)
                  roomj <- vapply(bj, function(b) if (is.na(b)) 0L else bin_room_remaining(b), integer(1))
                  if (any(roomj > 0L)) cnt <- cnt + 1L
                }
                alt_count[r] <- cnt
              }
              scarcity_bonus <- ifelse(alt_count <= 0L, w_scarce0,
                                       ifelse(alt_count == 1L, w_scarce1, 0.0))
            }
            
            # Make all score components exactly nrow(pool) long to avoid recycling warnings
            n_sc <- nrow(pool)
            rem_score    <- rep_len(as.numeric(rem_score),    n_sc)
            intl_bonus   <- rep_len(as.numeric(intl_bonus),   n_sc)
            infreq_bonus <- rep_len(as.numeric(infreq_bonus), n_sc)
            bin_bonus    <- rep_len(as.numeric(bin_bonus),    n_sc)
            scarcity_bonus <- rep_len(as.numeric(scarcity_bonus), n_sc)
            switch_pen   <- rep_len(as.numeric(switch_pen),   n_sc)
            spacing_pen  <- rep_len(as.numeric(spacing_pen),  n_sc)
            span_pen     <- rep_len(as.numeric(span_pen),     n_sc)
            min_bias     <- rep_len(if (isTRUE(min_left[i] > 0L)) (25000 + 500*as.integer(min_left[i])) else 0.0, n_sc)
            # --- underfill bonus (Months 1–2): strongly steer to reach the per-day floor (default 30) ---
            slot_used_i <- as.integer(assigned_day[[d]] %||% 0L)
            slot_cap_i  <- as.integer(day_caps[[d]] %||% 40L)
            min_i       <- if (month %in% c(1,2)) as.integer((min_per_day[[d]] %||% 30L)) else 0L
            floor_left  <- pmax(0L, min(min_i, slot_cap_i) - slot_used_i)
            cap_left_i  <- pmax(0L, slot_cap_i - slot_used_i)
            
            underfill_bonus <- rep_len(
              if (month %in% c(1, 2)) (as.numeric(floor_left) * 2000.0 + as.numeric(cap_left_i) * 300.0) else 0.0,
              n_sc
            )
            # --- Day "shadow price" toward target ~40 and same-day route-ledger bonus (Months 1–2) ---
            # Target per day is the cap for that day (default 40).
            day_target_i   <- as.integer((day_caps[[d]] %||% 40L))
            slot_used_i    <- as.integer(assigned_day[[d]] %||% 0L)
            shadow_deficit <- pmax(0L, day_target_i - slot_used_i)
            # Scaled pressure to lift underfilled days toward ~40 without overwhelming feasibility signals
            shadow_bonus <- rep_len(
              if (month %in% c(1,2)) as.numeric(shadow_deficit) * 180.0 else 0.0,
              n_sc
            )
            
            # --- Same-day route-aware ledger bonus: favor rows that still have room today on that URN ---
            # Compute how many surveys of each URN have already been assigned today across all slots.
            if (length(assignments)) {
              assigned_today_df <- tryCatch({
                df_all <- dplyr::bind_rows(lapply(assignments, function(xx) xx %||% tibble::tibble()))
                if (is.data.frame(df_all) && nrow(df_all)) df_all[df_all$Day == d, , drop = FALSE] else df_all[0, ]
              }, error = function(e) tibble::tibble()[0, ])
            } else {
              assigned_today_df <- tibble::tibble()[0, ]
            }
            
            used_today_map <- if (is.data.frame(assigned_today_df) && nrow(assigned_today_df)) {
              tmp <- stats::aggregate(assigned_today_df$`Assigned Surveys`,
                                      list(assigned_today_df$`Unique Route Number`), sum)
              setNames(as.integer(tmp$x), as.character(tmp$Group.1))
            } else setNames(integer(0), character(0))
            
            urn_vec    <- as.integer(pool$`Unique Route Number`)
            used_today <- {
              idx <- match(as.character(urn_vec), names(used_today_map))
              out <- integer(length(urn_vec)); out[] <- 0L
              ok  <- !is.na(idx)
              out[ok] <- as.integer(used_today_map[idx[ok]])
              out
            }
            
            rem_glob   <- pmax(0L, as.integer(pool$remaining %||% 0L))
            rem_today  <- pmax(0L, as.integer(rem_glob - used_today))
            # Clip by per-flight cap so we only count what this row could actually take
            ledger_clip <- pmin(as.integer(pmax(0L, raw_cap)), as.integer(rem_today))
            
            # Gentle nudge: prefer candidates that still have "today-room" on their URN
            per_f_cap_i <- as.integer(nzint(controls$per_flight_cap %||% 10L))
            ledger_today_bonus <- rep_len(
              if (month %in% c(1,2)) 80.0 * (as.numeric(ledger_clip) / pmax(1.0, as.numeric(per_f_cap_i))) else 0.0,
              n_sc
            )
            
            # Activation penalty (discourage scattering same route across many occurrences)
            urnv <- as.character(pool$`Unique Route Number`)
            cntv <- suppressWarnings(as.integer(route_used_count[urnv]))
            cntv[!is.finite(cntv)] <- 0L
            idx_init  <- match(as.integer(pool$`Unique Route Number`), route_initial_remaining$`Unique Route Number`)
            init_need <- ifelse(is.na(idx_init), NA, as.integer(route_initial_remaining$remaining[idx_init]))
            act_pen <- if (month == 3) {
              ifelse(
                cntv >= 1L & is.finite(init_need) & init_need <= per_f_cap,
                3.0,
                0.0
              )
            } else 0.0
            # Occurrence budget penalty (Months 1–2): prefer fewer flight-occurrences per URN
            # Budget: R<=10 -> 1 flight, 11-20 -> 2 flights, 21-30 -> 3 flights, else effectively unlimited
            occ_pen <- if (month %in% c(1, 2)) {
              budget <- ifelse(!is.finite(init_need), Inf,
                               ifelse(init_need <= 10L, 1L,
                                      ifelse(init_need <= 20L, 2L,
                                             ifelse(init_need <= 30L, 3L, 1e9))))
              pmax(0, as.numeric(cntv) - as.numeric(budget)) * 200.0
            } else 0.0
            # Consolidation bonus for Month 3 (finish routes with ≤10 remaining in one go when feasible)
            cons_bonus <- if (month == 3) {
              idxu <- match(as.integer(pool$`Unique Route Number`), route_remaining_local$`Unique Route Number`)
              remv <- ifelse(is.na(idxu), NA, as.integer(route_remaining_local$remaining[idxu]))
              ifelse(is.finite(remv) & remv > 0 & remv <= 10 & raw_cap >= remv, 500.0, 0.0)
            } else 0.0
            if (month == 3) {
              score <- rem_score + intl_bonus + infreq_bonus + bin_bonus + scarcity_bonus + cons_bonus - switch_pen - spacing_pen - span_pen - act_pen + min_bias + underfill_bonus
              
              # tiny random tie-breaker
              if (jitter_sd > 0) score <- score + stats::rnorm(n_sc, mean = 0, sd = jitter_sd)
            }
            
            # ---- Months 1–2 scoring override (Month 3 unchanged) ----
            if (month %in% c(1,2)) {
              n_sc <- nrow(pool)
              if (n_sc <= 0) {
                # NEW: make it explicit why -Inf will occur
                debug_note(d, i, "slot_no_candidates_score",
                           list(
                             pool_after_all_filters = as.integer(n_sc),
                             reason = "no survivors after window/latest/feasibility"
                           ))
                score <- rep(-Inf, 0L)
              } else {
                # Month-wide rarity (sc_n over first 28 days); default 28 if missing)
                sc_n <- if ("scarcity_n" %in% names(pool)) as.integer(pool$scarcity_n) else NA_integer_
                sc_n[is.na(sc_n)] <- 7L
                rarity <- 2000.0 / pmax(1L, sc_n)   # ↑ stronger: 4×/month = +500
                
                # International boost (when enabled): strong, with extra bonus for the
                # globally selected priority international URN (host route).
                # Heuristic: give a huge boost when the flight can take at least 2 surveys
                # (or the route only needs 1 left). Otherwise give a modest boost.
                intl <- if (isTRUE(controls$prior_intl)) {
                  ftv   <- tolower(as.character(pool$`Flight Type` %||% ""))
                  remv  <- pmax(0L, as.integer(pool$remaining %||% 0L))
                  capok <- (as.numeric(raw_cap %||% 0) >= 2) | (remv <= 1L)
                  base_intl <- ifelse(
                    ftv == "international",
                    ifelse(capok, 10000.0, 5000.0),
                    0.0
                  )
                  priority_urn <- suppressWarnings(as.integer(controls$priority_intl_urn %||% NA_integer_))
                  urnv <- suppressWarnings(as.integer(pool$`Unique Route Number` %||% NA_integer_))
                  priority_bonus <- ifelse(
                    is.finite(priority_urn) &
                      ftv == "international" &
                      is.finite(urnv) & (urnv == priority_urn),
                    50000.0,
                    0.0
                  )
                  base_intl + priority_bonus
                } else 0.0
                # Small remaining-need nudge
                remv <- pmax(0, as.integer(pool$remaining %||% 0L))
                rem_nudge <- 25.0 * (remv / as.numeric(max_rem %||% 1))
                
                # Adjacency (cluster builder) — nearest neighbors, wider halo
                # Build the list of already scheduled departures (this day/slot), sorted
                dep_sched <- if (is.data.frame(assignments[[i]]) && nrow(assignments[[i]])) {
                  o <- order(as.integer(assignments[[i]]$DepMin))
                  as.integer(assignments[[i]]$DepMin[o])
                } else integer(0)
                cc_sched <- if (is.data.frame(assignments[[i]]) && nrow(assignments[[i]])) {
                  o <- order(as.integer(assignments[[i]]$DepMin))
                  cclean(assignments[[i]]$Concourse[o])
                } else character(0)
                
                prev_last  <- as.numeric(prev_last_time)
                prev_first <- as.numeric(prev_first_time)
                last_cc    <- last_conc_clean
                first_cc   <- if (!is.null(first_conc[i]) && !is.na(first_conc[i])) cclean(first_conc[i]) else NA_character_
                same_last  <- pool$ConcourseClean == last_cc
                same_first <- pool$ConcourseClean == first_cc
                
                if (length(dep_sched)) {
                  idx_prev <- findInterval(as.integer(pool$DepMin), dep_sched)
                  prev_dep <- ifelse(idx_prev >= 1L, dep_sched[pmax(1L, idx_prev)], NA_integer_)
                  next_dep <- ifelse(idx_prev < length(dep_sched), dep_sched[pmin(length(dep_sched), idx_prev + 1L)], NA_integer_)
                  d_prev <- ifelse(is.na(prev_dep), NA_real_, pmax(0, as.numeric(pool$DepMin) - prev_dep))
                  d_next <- ifelse(is.na(next_dep), NA_real_, pmax(0, next_dep - as.numeric(pool$DepMin)))
                  
                  prev_cc <- ifelse(idx_prev >= 1L, cc_sched[pmax(1L, idx_prev)], NA_character_)
                  next_cc <- ifelse(idx_prev < length(cc_sched), cc_sched[pmin(length(cc_sched), idx_prev + 1L)], NA_character_)
                  
                  same_prev <- pool$ConcourseClean == prev_cc
                  same_next <- pool$ConcourseClean == next_cc
                  
                  # Wider halos: 60 min (same concourse) / 90 min (different)
                  prox_prev <- ifelse(is.na(d_prev), 0.0,
                                      ifelse(same_prev, pmax(0.0, 1.0 - d_prev/60.0),
                                             pmax(0.0, 1.0 - d_prev/90.0)))
                  prox_next <- ifelse(is.na(d_next), 0.0,
                                      ifelse(same_next, pmax(0.0, 1.0 - d_next/60.0),
                                             pmax(0.0, 1.0 - d_next/90.0)))
                  # Prefer hugging a neighbor; give a little extra if squeezed between two
                  prox <- pmin(1.5, pmax(prox_prev, prox_next) + 0.5 * pmin(prox_prev, prox_next))
                } else {
                  # Fallback to extremes for the very first commit on a day
                  d_after  <- if (is.finite(prev_last))  pmax(0, as.numeric(pool$DepMin) - prev_last) else NA_real_
                  d_before <- if (is.finite(prev_first)) pmax(0, prev_first - as.numeric(pool$DepMin)) else NA_real_
                  prox_after  <- ifelse(is.na(d_after),  0.0, ifelse(same_last,  pmax(0.0, 1.0 - d_after/60.0),
                                                                     pmax(0.0, 1.0 - d_after/90.0)))
                  prox_before <- ifelse(is.na(d_before), 0.0, ifelse(same_first, pmax(0.0, 1.0 - d_before/60.0),
                                                                     pmax(0.0, 1.0 - d_before/90.0)))
                  prox <- prox_after + prox_before
                }
                undercap <- as.numeric(pmax(0, as.integer(cap_left[[d]])) / pmax(1L, as.integer(day_caps[[d]] %||% 40L)))
                adjacency <- prox * undercap
                
                # Stronger clustering & completion incentives
                w_adj  <- 1400.0
                w_pile <- 60.0
                
                # Day fill pressure so underfilled days keep getting picks
                fill_pressure <- 400.0 * undercap
                
                # Refined pile-on (completion incentive only)
                row_cap  <- pmax(0L, pmin(as.integer(pool$remaining %||% 0L), as.integer(per_f_cap %||% 10L)))
                day_left <- pmax(0L, as.integer(day_caps[[d]] %||% 40L) - as.integer(assigned_day[[d]] %||% 0L))
                assignable0 <- pmax(0L, pmin(row_cap, day_left))
                urn_rem <- pmax(0L, as.integer(pool$remaining %||% 0L))
                more_on <- ifelse(assignable0 >= urn_rem & urn_rem > 0L, 1.0,
                                  ifelse(urn_rem <= as.integer(per_f_cap %||% 10L) & urn_rem > 0L,
                                         assignable0 / pmax(1, urn_rem),
                                         pmax(0, assignable0 - 1) / pmax(1, as.integer(per_f_cap %||% 10L) - 1)))
                
                # Concourse change penalty with ±60-min halo (reduced)
                change_flag <- pool$ConcourseClean != last_cc
                halo <- if (is.finite(as.numeric(last_change_time[i] %||% NA))) {
                  abs(as.numeric(pool$DepMin) - as.numeric(last_change_time[i])) <= 60
                } else FALSE
                conc_pen <- 2.0 * (as.numeric(change_flag) + as.numeric(change_flag & halo))
                # If the day is <90% filled and this candidate would add only a small amount (<=3),
                # amplify the change-penalty to prefer same-concourse (reduces walking for 2–3 survey sprinkles).
                day_cap_here <- as.integer(day_caps[[d]] %||% 40L)
                day_fill     <- as.integer(assigned_day[[d]] %||% 0L)
                fill_frac    <- if (day_cap_here > 0L) (day_fill / day_cap_here) else 0
                smallish     <- as.integer(pmax(0L, pmin(row_cap, pmax(0L, day_cap_here - day_fill)))) <= 3L
                if (is.finite(fill_frac) && (fill_frac < 0.90) && isTRUE(smallish)) {
                  conc_pen <- conc_pen * 2.0
                }
                
                # --- Balance guidance (no hard blocks) ---
                # Same-strength bonuses for AM/PM and Weekend/Weekday; if both are needed,
                # a weekend PM gets both bonuses and rises to the top.
                is_we_vec <- (d %in% WEEKEND_DAYS)
                is_am_vec <- as.logical(pool$AM %||% (as.numeric(pool$DepMin) < 12*60))
                
                cnt <- global_am_pm_counts()
                tot_now <- as.integer(cnt$tot %||% 0L)
                tg <- get_targets()
                
                B <- 12000.0  # strong steering toward AM/PM only (Weekend% steering removed)
                we_bonus <- rep(0.0, n_sc)
                
                # AM/PM steering (respects split vs global target)
                am_bonus <- rep(0.0, n_sc)
                if (!isTRUE(tg$split)) {
                  am_t <- (as.numeric(tg$am_global %||% 45)) / 100
                  cur_am <- as.integer(cnt$am %||% 0L)
                  cur_frac <- if (tot_now > 0) cur_am / tot_now else am_t
                  low_am <- am_t - 0.10; high_am <- am_t + 0.10
                  need_more_am <- cur_frac < low_am
                  need_less_am <- cur_frac > high_am
                  am_bonus <- if (need_more_am) {
                    ifelse(is_am_vec, B, 0.0)
                  } else if (need_less_am) {
                    ifelse(!is_am_vec, B, 0.0)
                  } else rep(0.0, n_sc)
                } else {
                  if (is_we_vec) {
                    tot0 <- as.integer(cnt$tot_we %||% 0L); am0 <- as.integer(cnt$am_we %||% 0L)
                    am_t <- (as.numeric(tg$am_we %||% 45)) / 100
                    frac <- if (tot0 > 0) am0 / tot0 else am_t
                    low_am <- am_t - 0.10; high_am <- am_t + 0.10
                    need_more_am <- frac < low_am
                    need_less_am <- frac > high_am
                    am_bonus <- if (need_more_am) {
                      ifelse(is_am_vec, B, 0.0)
                    } else if (need_less_am) {
                      ifelse(!is_am_vec, B, 0.0)
                    } else rep(0.0, n_sc)
                  } else {
                    tot0 <- as.integer(cnt$tot_wd %||% 0L); am0 <- as.integer(cnt$am_wd %||% 0L)
                    am_t <- (as.numeric(tg$am_wd %||% 45)) / 100
                    frac <- if (tot0 > 0) am0 / tot0 else am_t
                    low_am <- am_t - 0.10; high_am <- am_t + 0.10
                    need_more_am <- frac < low_am
                    need_less_am <- frac > high_am
                    am_bonus <- if (need_more_am) {
                      ifelse(is_am_vec, B, 0.0)
                    } else if (need_less_am) {
                      ifelse(!is_am_vec, B, 0.0)
                    } else rep(0.0, n_sc)
                  }
                }
                
                # First-pick shove (Months 1–2):
                # If this day has no assignments yet and the mix is out of band,
                # strongly prefer the needed side (AM or PM) for this day’s FIRST pick.
                seed_bonus <- rep(0.0, n_sc)
                if (month %in% c(1, 2) && !is.finite(first_time[i])) {
                  cnt <- global_am_pm_counts()
                  tot_now <- as.integer(cnt$tot %||% 0L)
                  if (is.finite(tot_now)) {
                    Bseed <- 26000.0
                    tg <- get_targets()
                    # Compute current vs target AM%
                    if (!isTRUE(tg$split)) {
                      am_t <- (as.numeric(tg$am_global %||% 45)) / 100
                      cur  <- if (tot_now > 0) (as.numeric(cnt$am %||% 0L) / tot_now) else am_t
                    } else if (d %in% c("Sat","Sun")) {
                      tot0 <- as.integer(cnt$tot_we %||% 0L); am0 <- as.integer(cnt$am_we %||% 0L)
                      am_t <- (as.numeric(tg$am_we %||% 45)) / 100
                      cur  <- if (tot0 > 0) am0 / tot0 else am_t
                    } else {
                      tot0 <- as.integer(cnt$tot_wd %||% 0L); am0 <- as.integer(cnt$am_wd %||% 0L)
                      am_t <- (as.numeric(tg$am_wd %||% 45)) / 100
                      cur  <- if (tot0 > 0) am0 / tot0 else am_t
                    }
                    if (cur > (am_t + 0.08)) {
                      # too many AM → shove PM for first pick
                      seed_bonus <- ifelse(!is_am_vec, Bseed, 0.0)
                    } else if (cur < (am_t - 0.08)) {
                      # too few AM → shove AM for first pick
                      seed_bonus <- ifelse(is_am_vec, Bseed, 0.0)
                    }
                  }
                }
                
                # Final score (Months 1–2) with steering (no hard skips)
                adjacency[!is.finite(adjacency)] <- 0.0
                rarity[!is.finite(rarity)]       <- 0.0
                rem_nudge[!is.finite(rem_nudge)] <- 0.0
                conc_pen[!is.finite(conc_pen)]   <- 0.0
                # Big reward for finishing a route in one pick (Months 1–2)
                finish_bonus <- {
                  idxu <- match(as.integer(pool$`Unique Route Number`), route_remaining_local$`Unique Route Number`)
                  remv <- ifelse(is.na(idxu), NA, as.integer(route_remaining_local$remaining[idxu]))
                  ifelse(is.finite(remv) & remv > 0 & raw_cap >= remv, 8000.0, 0.0)
                }
                score <- intl + rarity + rem_nudge + (w_adj * adjacency + w_pile * more_on) + fill_pressure - conc_pen + we_bonus + am_bonus + underfill_bonus - occ_pen + finish_bonus + infreq_bonus
                
                # Tiny jitter
                if (month %in% c(1,2)) score <- score + seed_bonus
                if (jitter_sd > 0) score <- score + stats::rnorm(length(score), mean = 0, sd = jitter_sd)
                # Deterministic rarity tiebreak (rarer routes win exact ties; no constraint changes)
                f2 <- pmax(1L, pmin(7L, as.integer(pool$freq %||% NA_integer_)))
                f2[is.na(f2)] <- 7L
                tiebreak_eps <- ((7 - f2) / 6.0) * 1e-2
                score <- score + shadow_bonus + ledger_today_bonus + tiebreak_eps
                # Soft preferences ONLY (no filtering): planned window + prefer-side (AM/PM)
                planned_bonus <- rep(0.0, length(score))
                pw_all <- state$slot_windows %||% list()
                pw <- if (length(pw_all) >= i) pw_all[[i]] else NULL
                if (!is.null(pw) && length(pw) && is.finite(as.integer(pw$start)) && is.finite(as.integer(pw$end))) {
                  ws <- as.integer(pw$start); we <- as.integer(pw$end)
                  planned_bonus <- ifelse(as.integer(pool$DepMin) >= ws & as.integer(pool$DepMin) <= we, 500.0, 0.0)
                }
                
                prefer_side_bonus <- rep(0.0, length(score))
                if (!is.null(prefer_side) && length(score)) {
                  is_am_side <- as.logical(pool$AM %||% (as.integer(pool$DepMin) < 12L*60L))
                  if (identical(prefer_side, "AM")) {
                    prefer_side_bonus <- ifelse(is_am_side, 800.0, 0.0)
                  } else if (identical(prefer_side, "PM")) {
                    prefer_side_bonus <- ifelse(!is_am_side, 800.0, 0.0)
                  }
                }
                
                score <- score + planned_bonus + prefer_side_bonus
                # >>> NEW: ledger-based steering override + spacing-aware pack estimate (Months 1–2) <<<
                if (month %in% c(1,2)) {
                  # Keep the old steering around so we can subtract it out
                  am_bonus_old <- if (exists("am_bonus")) am_bonus else rep(0.0, length(score))
                  
                  # Inputs we need
                  is_am_vec <- as.logical(pool$AM %||% (as.numeric(pool$DepMin) < 12*60))
                  cnt <- global_am_pm_counts()
                  tg <- get_targets()
                  
                  # Determine where the ledger is short (global or split)
                  need_pm <- FALSE; need_am <- FALSE
                  if (!isTRUE(tg$split)) {
                    am_t <- (as.numeric(tg$am_global %||% 45)) / 100
                    tot0 <- as.integer(cnt$tot %||% 0L)
                    am0  <- as.integer(cnt$am  %||% 0L)
                    cur  <- if (tot0 > 0L) am0 / tot0 else am_t
                    need_pm <- (cur > (am_t + 0.03))
                    need_am <- (cur < (am_t - 0.03))
                  } else {
                    if (is_weekend(d)) {
                      am_t <- (as.numeric(tg$am_we %||% 45)) / 100
                      tot0 <- as.integer(cnt$tot_we %||% 0L); am0 <- as.integer(cnt$am_we %||% 0L)
                    } else {
                      am_t <- (as.numeric(tg$am_wd %||% 45)) / 100
                      tot0 <- as.integer(cnt$tot_wd %||% 0L); am0 <- as.integer(cnt$am_wd %||% 0L)
                    }
                    cur  <- if (tot0 > 0L) am0 / tot0 else am_t
                    need_pm <- (cur > (am_t + 0.03))
                    need_am <- (cur < (am_t - 0.03))
                  }
                  
                  # First picks of the day: go pure to fix the ledger
                  assigned_so_far_local <- as.integer(assigned_day[[d]] %||% 0L)
                  lock_n <- as.integer((day_caps[[d]] %||% 40L)) # hold pure-side steering until day is basically full
                  B  <- 22000.0
                  B2 <- 0.25 * B
                  
                  # Identify AM/PM candidates for this pool
                  is_am_vec <- as.logical(pool$AM %||% (as.numeric(pool$DepMin) < 12L*60L))
                  has_am    <- any(is_am_vec, na.rm = TRUE)
                  has_pm    <- any(!is_am_vec, na.rm = TRUE)
                  
                  am_bonus2 <- rep(0.0, length(score))
                  
                  # When significantly out-of-band early in the slot, hard-mask the wrong side
                  # for a few picks so we don't drift all-PM or all-AM.
                  early_n <- min(14L, lock_n) # only the first few picks
                  if (month %in% c(1L,2L) && assigned_so_far_local < early_n) {
                    if (isTRUE(need_am) && has_am) {
                      # Need AM: forbid PM *temporarily* if at least one AM exists
                      am_bonus2 <- ifelse(!is_am_vec, -1e9, 0.0)
                    } else if (isTRUE(need_pm) && has_pm) {
                      # Need PM: forbid AM *temporarily* if at least one PM exists
                      am_bonus2 <- ifelse(is_am_vec, -1e9, 0.0)
                    }
                  }
                  
                  # If we didn't hard-mask (or after early_n), use the gentler nudges you had
                  if (all(am_bonus2 == 0.0)) {
                    if (assigned_so_far_local < lock_n) {
                      if (isTRUE(need_pm)) {
                        am_bonus2 <- ifelse(!is_am_vec, B, -2*B)
                      } else if (isTRUE(need_am)) {
                        am_bonus2 <- ifelse(is_am_vec, B, -2*B)
                      }
                    } else {
                      if (isTRUE(need_pm)) {
                        am_bonus2 <- ifelse(!is_am_vec, B2, 0.0)
                      } else if (isTRUE(need_am)) {
                        am_bonus2 <- ifelse(is_am_vec, B2, 0.0)
                      }
                    }
                  }
                  
                  # Spacing-aware packability (upper-bound heuristic around each candidate) — unchanged
                  span_len <- as.integer(pmax(1L, nzint(day_hours_caps[i] %||% controls$max_hours %||% 6L))) * 60L
                  half_win <- as.integer(span_len / 2L)
                  depv <- as.integer(pool$DepMin)
                  pack_neighbors <- vapply(seq_along(depv), function(r){
                    lo <- depv[r] - half_win; hi <- depv[r] + half_win
                    sum(depv >= lo & depv <= hi) - 1L
                  }, integer(1))
                  pack_score <- 20.0 * pmin(40L, as.numeric(pack_neighbors))
                  
                  # Override steering and add packability
                  score <- score - am_bonus_old + am_bonus2 + pack_score
                  # Band penalty: strongly discourage choices that would push AM% outside ±10% once we're past the ramp threshold,
                  # but never fully zero out the slot. Make it a very large negative *penalty* instead of -Inf.
                  if (month %in% c(1L, 2L)) {
                    tg <- get_targets()
                    # Determine AM/PM side for each candidate row in 'pool'
                    is_am_vec <- as.logical(pool$AM %||% (as.numeric(pool$DepMin) < 12L*60L))
                    we_flag   <- isTRUE(is_weekend(d))
                    
                    # If we have enough total placed to start enforcing, penalize candidates that would violate the bands.
                    cnt <- global_am_pm_counts()
                    tot_now <- as.integer(cnt$tot %||% 0L)
                    
                    if (tot_now >= band_threshold) {
                      # Never zero out a slot: bypass bands if (a) the slot is still underfilled
                      # or (b) the pool has only one side (AM-only or PM-only).
                      slot_used_i <- as.integer(assigned_day[[d]] %||% 0L)
                      slot_cap_i  <- as.integer((day_caps[[i]] %||% 40L))
                      min_i       <- as.integer((min_per_day[[d]] %||% 30L))
                      underfilled <- slot_used_i < max(min_i, floor(0.5 * slot_cap_i))
                      one_side_only <- (!has_am) || (!has_pm)
                      
                      bad_mask <- vapply(
                        is_am_vec,
                        function(am_one) would_violate_bands(we_flag, isTRUE(am_one), 1L),
                        logical(1)
                      )
                      
                      if (!underfilled && !one_side_only && any(bad_mask, na.rm = TRUE)) {
                        # Large but finite penalty: keep candidates in the pool so the slot never goes empty,
                        # but make them much less attractive than in-band choices.
                        band_penalty <- 20000.0
                        score[bad_mask] <- score[bad_mask] - band_penalty
                      }
                    }
                  }
                  
                  debug_note(
                    d, i, "score_ledger_override",
                    list(
                      need_pm = isTRUE(need_pm),
                      need_am = isTRUE(need_am),
                      assigned_so_far = as.integer(assigned_so_far_local),
                      lock_n = as.integer(lock_n),
                      
                      # Band enforcement visibility (helps explain why candidates get -Inf)
                      band_threshold   = as.integer(band_threshold),
                      band_tot_now     = as.integer(tot_now),
                      band_rule_active = as.integer(isTRUE(tot_now >= band_threshold)),
                      
                      band_underfilled   = if (exists("underfilled", inherits = FALSE)) as.integer(isTRUE(underfilled)) else NA_integer_,
                      band_one_side_only = if (exists("one_side_only", inherits = FALSE)) as.integer(isTRUE(one_side_only)) else NA_integer_,
                      band_bad_n         = if (exists("bad_mask", inherits = FALSE)) as.integer(sum(bad_mask, na.rm = TRUE)) else NA_integer_,
                      band_mask_applied  = if (exists("bad_mask", inherits = FALSE) &&
                                               exists("underfilled", inherits = FALSE) &&
                                               exists("one_side_only", inherits = FALSE)) {
                        as.integer((!underfilled && !one_side_only && any(bad_mask, na.rm = TRUE)))
                      } else {
                        NA_integer_
                      }
                    )
                  )
                }
              }
            }
            # Debug: trace score components for the debug URN vs the slot winner
            if (is.finite(as.integer(state$debug_urn %||% NA_integer_))) {
              trace_urn <- as.integer(state$debug_urn %||% NA_integer_)
              urn_col <- if ("Unique Route Number" %in% names(pool)) {
                suppressWarnings(as.integer(pool$`Unique Route Number`))
              } else if ("URN" %in% names(pool)) {
                suppressWarnings(as.integer(pool$URN))
              } else {
                rep(NA_integer_, nrow(pool))
              }
              trace_rows <- which(is.finite(urn_col) & urn_col == trace_urn)
              best_idx_local <- if (length(score)) which.max(score) else NA_integer_
              
              if (length(trace_rows)) {
                for (idx in trace_rows) {
                  debug_note(
                    d, i, "slot_score_trace",
                    list(
                      trace_urn        = trace_urn,
                      row_index        = as.integer(idx),
                      row_dep_min      = as.integer(pool$DepMin[idx]),
                      row_cap          = as.integer(raw_cap[idx]),
                      row_score        = as.numeric(score[idx]),
                      row_rem_score    = as.numeric(if (exists("rem_score")) rem_score[idx] else NA_real_),
                      row_intl_bonus   = as.numeric(if (exists("intl_bonus")) intl_bonus[idx] else NA_real_),
                      row_infreq_bonus = as.numeric(if (exists("infreq_bonus")) infreq_bonus[idx] else NA_real_)
                    )
                  )
                }
              } else if (nrow(pool) > 0L) {
                debug_note(
                  d, i, "slot_score_trace_absent",
                  list(
                    trace_urn = trace_urn,
                    pool_size = as.integer(nrow(pool))
                  )
                )
              }
              
              if (is.finite(best_idx_local) &&
                  best_idx_local >= 1L && best_idx_local <= nrow(pool)) {
                debug_note(
                  d, i, "slot_score_winner",
                  list(
                    winner_urn     = as.integer(urn_col[best_idx_local]),
                    winner_dep_min = as.integer(pool$DepMin[best_idx_local]),
                    winner_cap     = as.integer(raw_cap[best_idx_local]),
                    winner_score   = as.numeric(score[best_idx_local])
                  )
                )
              }
            }
            pick_idx <- which.max(score)
            sc <- if (length(pick_idx)) score[pick_idx] else -Inf
            if (is.finite(sc) && sc > best_score) {
              best <- list(day_index = i, day_name = d, pool = pool, pick_idx = pick_idx, raw_cap = raw_cap, score = score)
              best_score <- sc
            }
          } # for i
          debug_note("ALL", NA, "iter_best",
                     list(
                       best_ok    = as.character(!is.null(best)),
                       best_score = as.numeric(best_score)
                     ))
          
          if (is.null(best)) break
          
          i <- best$day_index; d <- best$day_name
          pool <- best$pool
          # Keep a local copy of the scores so we can try the next-best on THIS day if the top pick fails spacing
          loc_score <- tryCatch(best$score, error = function(e) NULL)
          if (is.null(loc_score) || length(loc_score) != nrow(pool)) loc_score <- rep(0, nrow(pool))
          
          repeat {
            # pick the current best within this day/pool
            pick_idx <- if (length(loc_score)) which.max(loc_score) else NA_integer_
            if (!is.finite(pick_idx) || !length(pick_idx) || is.na(pick_idx) || !is.finite(loc_score[pick_idx]) || loc_score[pick_idx] == -Inf) break
            
            row_cap <- as.integer(best$raw_cap[pick_idx])
            pick_row <- pool[pick_idx,,drop=FALSE]
            
            pools_now <- current_bin_pools(d)
            # Reservation heuristic toward AM/PM targets (Months 1–2 only): keep headroom so we don't blow AM early
            guide_left <- 1e9L
            if (month %in% c(1,2)) {
              guide_left <- as.integer(band_room_for(is_weekend(d), isTRUE(pick_row$AM)))
            }
            # If we're steering the day toward a pure AM or pure PM window, don't let guide_left restrict the placement.
            # This preserves your AM/PM weekly ledger while allowing pure windows to fully pack.
            if (month %in% c(1,2) && exists("prefer_side") && !is.null(prefer_side)) {
              guide_left <- 1000000000L
            }
            
            if (month == 3 && !is.null(bin_caps)) {
              bname <- as.character(pick_row$bin[[1]]); room_b <- if (is.na(bname)) 0L else bin_room_remaining(bname)
            } else room_b <- 1e9L
            
            # Hard AM/PM pool room remaining for this pick (Months 1–2 only)
            room_ampm <- 1e9L
            if (isTRUE(hard_ampm) && month %in% c(1,2)) {
              if (!isTRUE(am_controls$split)) {
                room_ampm <- as.integer(if (isTRUE(pick_row$AM)) (ampm_left$AM %||% 0L) else (ampm_left$PM %||% 0L))
              } else {
                if (is_weekend(d)) {
                  room_ampm <- as.integer(if (isTRUE(pick_row$AM)) (ampm_left$AM_we %||% 0L) else (ampm_left$PM_we %||% 0L))
                } else {
                  room_ampm <- as.integer(if (isTRUE(pick_row$AM)) (ampm_left$AM_wk %||% 0L) else (ampm_left$PM_wk %||% 0L))
                }
              }
            }
            max_day_left <- pmax(0L, as.integer(day_caps[[d]] %||% 40L) - assigned_day[[d]])
            assignable <- max(0L,
                              min(
                                as.integer(row_cap),
                                as.integer(cap_left[[d]]),
                                as.integer(max_day_left),
                                as.integer(room_b),
                                as.integer(room_ampm)
                              ))
            urn_rem_now <- as.integer(pick_row$remaining %||% 0L)
            if (isTRUE(assignable == 1L) && urn_rem_now > 1L) {
              # lift up to what this row can genuinely take (bounded by row_cap & day caps)
              target_lift <- as.integer(min(urn_rem_now, row_cap))
              assignable <- max(0L, min(
                target_lift,
                as.integer(cap_left[[d]]),
                as.integer(max_day_left),
                as.integer(room_b),
                as.integer(room_ampm)
              ))
            }
            debug_note(d, i, "assignable_calc",
                       list(
                         row_cap    = as.integer(row_cap),
                         guide_left = as.integer(guide_left),
                         cap_left   = as.integer(cap_left[[d]]),
                         day_left   = as.integer(max_day_left),
                         room_b     = as.integer(room_b),
                         room_ampm  = as.integer(room_ampm),
                         assignable = as.integer(assignable)
                       ))
            if (assignable <= 0L) {
              # mark used locally and move to next best within this day
              cur_used <- if (i <= length(used_idx) && length(used_idx[[i]])) used_idx[[i]] else {
                nr <- tryCatch(nrow(day_cands[[i]]), error = function(e) 0L)
                rep(FALSE, if (is.finite(nr) && nr > 0L) nr else 0L)
              }
              local_mask <- which(!cur_used)
              if (length(local_mask) >= pick_idx) {
                cur_used[local_mask[pick_idx]] <- TRUE
                used_idx[[i]] <- cur_used
              }
              loc_score[pick_idx] <- -Inf
              next
            }
            
            out_row <- tibble::tibble(
              Day = d,
              Airline = pick_row$Airline %||% NA_character_,
              Concourse = pick_row$Concourse %||% NA_character_,
              Gate = NA_character_,
              Destination = pick_row$Destination %||% NA_character_,
              `Flight #` = pick_row$`Flight #` %||% NA_character_,
              `Departure Time` = pick_row$`Departure Time` %||% NA_character_,
              `Assigned Surveys` = as.integer(assignable),
              `Flight Type` = pick_row$`Flight Type` %||% NA_character_,
              `Airline Code` = pick_row$`Airline Code` %||% NA_character_,
              `Unique Route Number` = pick_row$`Unique Route Number` %||% NA_integer_,
              DepMin = as.integer(pick_row$DepMin),
              `Destination Code` = pick_row$`Destination Code` %||% NA_character_
            )
            
            allow_commit <- TRUE
            
            # minutes cap for this slot (fine-tune per-slot > global > default 6)
            cap_min_ii <- as.integer(pmax(1L, as.integer(day_hours_caps[i] %||% controls$max_hours %||% 6L)) * 60L)
            
            if (isTRUE(hard_hours_flags[i]) && is.finite(cap_min_ii)) {
              # Prospective span if we add this pick
              t_dep   <- as.integer(pick_row$DepMin)
              t_first <- if (is.finite(first_time[i])) pmin(first_time[i], t_dep) else t_dep
              t_last  <- if (is.finite(max_time[i]))   pmax(max_time[i],   t_dep) else t_dep
              t_span  <- as.integer(t_last - t_first)
              
              if (t_span > cap_min_ii) {
                allow_commit <- FALSE
                # record diagnostics for this day label (e.g. "Sun")
                urn_block <- as.integer(pick_row$`Unique Route Number`[is.finite(pick_row$`Unique Route Number`)])
                if (!length(bypass_acc_loc$hard_hours_blocked[[d]])) bypass_acc_loc$hard_hours_blocked[[d]] <- integer(0)
                bypass_acc_loc$hard_hours_blocked[[d]] <- unique(c(bypass_acc_loc$hard_hours_blocked[[d]], urn_block))
              }
            }
            
            if (isTRUE(allow_commit) && (month %in% c(1L, 2L) || isTRUE(input$enforce_spacing))) {
              sched_i <- assignments[[i]]; if (!is.data.frame(sched_i)) sched_i <- tibble::tibble()
              preview <- dplyr::bind_rows(sched_i, out_row) %>% dplyr::arrange(DepMin)
              dep  <- as.integer(preview$DepMin)
              conc <- cclean(preview$Concourse)
              Sv   <- as.integer(preview$`Assigned Surveys`)
              
              # Locate the inserted row by DepMin; fallback by URN match if needed
              pos <- which(dep == as.integer(pick_row$DepMin))[1]
              if (!is.finite(pos)) {
                pos <- which(as.integer(preview$`Unique Route Number`) == as.integer(pick_row$`Unique Route Number`) &
                               dep == as.integer(pick_row$DepMin))[1]
              }
              spacing_ok_prev <- TRUE
              spacing_ok_next <- TRUE
              if (length(pos) && is.finite(pos)) {
                if (pos > 1) {
                  need_prev <- spacing_after(Sv[pos-1], conc[pos-1] != conc[pos])
                  spacing_ok_prev <- dep[pos] >= (dep[pos-1] + as.integer(need_prev))
                }
                if (pos < length(dep)) {
                  need_next <- spacing_after(Sv[pos], conc[pos] != conc[pos+1])
                  spacing_ok_next <- dep[pos+1] >= (dep[pos] + as.integer(need_next))
                }
                if (!(isTRUE(spacing_ok_prev) && isTRUE(spacing_ok_next))) {
                  allow_commit <- FALSE
                  debug_note(d, i, "slot_commit_blocked_spacing",
                             list(
                               pos      = as.integer(pos %||% NA_integer_),
                               dep_prev = as.integer(if (length(pos) && pos>1) dep[pos-1] else NA),
                               dep_this = as.integer(if (length(pos)) dep[pos] else NA),
                               dep_next = as.integer(if (length(pos) && pos<length(dep)) dep[pos+1] else NA)
                             ))
                  # bump stall counter for this day
                  state$stall_counts <- { x <- (state$stall_counts %||% rep(0L, length(days))); x[i] <- x[i] + 1L; x }
                  
                  # ---- Adaptive survey sizing: only the NEXT side can be helped by shrinking Sv[pos] ----
                  if (isTRUE(spacing_ok_prev) && isTRUE(pos < length(dep))) {
                    gap_next   <- as.integer(dep[pos+1] - dep[pos])
                    next_switch <- conc[pos] != conc[pos+1]
                    s_curr <- as.integer(Sv[pos])
                    s_fit  <- s_curr
                    while (s_fit >= 2L) {
                      need_try <- spacing_after(s_fit, next_switch)
                      if (gap_next >= as.integer(need_try)) break
                      s_fit <- s_fit - 1L
                    }
                    if (s_fit >= 2L && s_fit < s_curr) {
                      assignable <- as.integer(s_fit)
                      out_row$`Assigned Surveys` <- as.integer(assignable)
                      Sv[pos] <- as.integer(s_fit)
                      allow_commit <- TRUE
                      debug_note(d, i, "slot_commit_sized_down",
                                 list(from = as.integer(s_curr), to = as.integer(s_fit), gap_next = as.integer(gap_next)))
                    }
                  }
                  
                  # ---- Feasibility-aware local filter on THIS day: drop infeasible candidates now ----
                  if (!isTRUE(allow_commit) && nrow(pool) > 0L && length(dep) >= 1L) {
                    # Remove current trial from the neighbor arrays
                    dep_no  <- if (length(dep)  >= pos) dep[-pos]  else dep
                    conc_no <- if (length(conc) >= pos) conc[-pos] else conc
                    Sv_no   <- if (length(Sv)   >= pos) Sv[-pos]   else Sv
                    
                    feas_mask <- rep_len(FALSE, nrow(pool))
                    day_left <- pmax(0L, as.integer(day_caps[[d]] %||% 40L) - sum(Sv_no, na.rm = TRUE))
                    
                    for (jj in seq_len(nrow(pool))) {
                      c_dep <- as.integer(pool$DepMin[jj])
                      pj <- 1L + findInterval(c_dep, dep_no)
                      
                      ok_prev <- TRUE
                      if (pj > 1L) {
                        prev_switch_j <- (cclean(pool$Concourse[jj]) != conc_no[pj-1L])
                        need_prev_j   <- spacing_after(Sv_no[pj-1L], prev_switch_j)
                        ok_prev       <- c_dep >= (dep_no[pj-1L] + as.integer(need_prev_j))
                      }
                      
                      ok_next <- TRUE
                      # Max surveys that can fit before the NEXT neighbor, given spacing_after() tail
                      if (pj <= length(dep_no)) {
                        next_switch_j <- (cclean(pool$Concourse[jj]) != conc_no[pj])
                        gap_next_j    <- as.integer(dep_no[pj] - c_dep)
                        bonus_next    <- if (isTRUE(next_switch_j)) 15L else 0L
                        M             <- as.integer(gap_next_j - bonus_next)
                        max_pairs     <- if (M >= 0L) as.integer(floor(M / 10)) else 0L
                        s_fit_next    <- pmax(0L, as.integer(2L * max_pairs))
                      } else {
                        s_fit_next <- 1e9L  # no next flight
                      }
                      # Respect remaining, per-flight, and per-day caps too
                      s_cap <- as.integer(min(raw_cap[jj], day_left, s_fit_next))
                      ok_next <- (s_cap >= 1L)
                      # Trim raw_cap so scoring/assignment won’t exceed what spacing allows
                      raw_cap[jj] <- as.integer(min(raw_cap[jj], s_cap))
                      feas_mask[jj] <- isTRUE(ok_prev && ok_next)
                    }
                    
                    if (any(feas_mask)) {
                      bad <- which(!feas_mask)
                      if (length(bad)) loc_score[bad] <- -Inf
                      debug_note(d, i, "slot_local_feasible_filter",
                                 list(kept = as.integer(sum(feas_mask)),
                                      dropped = as.integer(sum(!feas_mask))))
                    } else {
                      debug_note(d, i, "slot_local_no_feasible", list(pool_n = as.integer(nrow(pool))))
                    }
                  }
                } else {
                  debug_note(d, i, "slot_commit_spacing_ok", list(pos = as.integer(pos)))
                }
              }
            }
            
            # --- Month-3 hard bin cap guard (clamp or block) ---
            if (month == 3 && !is.null(bin_caps)) {
              bname <- flight_bin(as.character(d), as.integer(pick_row$DepMin))
              if (is.character(bname) && nzchar(bname) &&
                  !is.null(bin_caps[[bname]]) && is.finite(as.numeric(bin_caps[[bname]]))) {
                used_now <- as.integer(live_bins_loc[[bname]] %||% 0L)
                cap_now  <- as.integer(bin_caps[[bname]] %||% 0L)
                room_now <- pmax(0L, cap_now - used_now)
                
                if (room_now <= 0L) {
                  allow_commit <- FALSE
                } else if (assignable > room_now) {
                  assignable <- as.integer(room_now)
                  out_row$`Assigned Surveys` <- as.integer(assignable)
                }
              }
            }
            if (isTRUE(allow_commit)) {
              # ---- COMMIT: add the row and update all book-keeping ----
              assignments[[i]] <- dplyr::bind_rows(assignments[[i]] %||% tibble::tibble(), out_row)
              did_commit <- TRUE
              # Month-3: increment realized bin counts
              if (month == 3) {
                bname_upd <- flight_bin(as.character(d), as.integer(pick_row$DepMin))
                if (is.character(bname_upd) && nzchar(bname_upd)) {
                  live_bins_loc[[bname_upd]] <- as.integer(live_bins_loc[[bname_upd]] %||% 0L) + as.integer(assignable)
                }
              }
              
              assigned_day[[d]] <- assigned_day[[d]] + assignable
              cap_left[[d]]     <- cap_left[[d]]     - assignable
              min_left[[d]]     <- pmax(0L, min_left[[d]] - assignable)
              
              if (isTRUE(hard_ampm)) {
                if (!isTRUE(am_controls$split)) {
                  if (isTRUE(pick_row$AM)) ampm_left$AM <- max(0L, (ampm_left$AM %||% 0L) - assignable)
                  if (isTRUE(pick_row$PM)) ampm_left$PM <- max(0L, (ampm_left$PM %||% 0L) - assignable)
                } else {
                  if (is_weekend(d)) {
                    if (isTRUE(pick_row$AM)) ampm_left$AM_we <- max(0L, (ampm_left$AM_we %||% 0L) - assignable)
                    if (isTRUE(pick_row$PM)) ampm_left$PM_we <- max(0L, (ampm_left$PM_we %||% 0L) - assignable)
                  } else {
                    if (isTRUE(pick_row$AM)) ampm_left$AM_wk <- max(0L, (ampm_left$AM_wk %||% 0L) - assignable)
                    if (isTRUE(pick_row$PM)) ampm_left$PM_wk <- max(0L, (ampm_left$PM_wk %||% 0L) - assignable)
                  }
                }
              }
              # Track realized AM/PM counts for the hard-cap feasibility guard
              if (month %in% c(1,2) && !isTRUE(am_controls$split)) {
                if (isTRUE(pick_row$AM)) global_am <- global_am + as.integer(assignable)
                if (isTRUE(pick_row$PM)) global_pm <- global_pm + as.integer(assignable)
              }
              urn_key <- as.character(pick_row$`Unique Route Number`)
              if (!is.na(urn_key)) { route_used_count[urn_key] <- as.integer((route_used_count[urn_key] %||% 0L) + 1L) }
              
              # decrement remaining on this URN
              ridx <- match(pick_row$`Unique Route Number`, route_remaining_local$`Unique Route Number`)
              if (!is.na(ridx)) route_remaining_local$remaining[ridx] <- pmax(0L, route_remaining_local$remaining[ridx] - assignable)
              
              # update timeline stats
              last_time[i] <- as.integer(pick_row$DepMin)              # last pick (for spacing)
              if (!is.finite(first_time[i])) first_time[i] <- last_time[i]
              first_time[i] <- pmin(first_time[i], last_time[i])       # maintain min
              max_time[i]   <- pmax(max_time[i], last_time[i])         # maintain true max
              
              # track first-concourse and concourse-change time (±90-min halo)
              prev_conc_old <- as.character(last_conc[i] %||% NA_character_)
              if (!is.finite(first_time[i])) {
                # first placement on this day captures "first_conc"
                first_conc[i] <- as.character(pick_row$Concourse)
              }
              if (!is.na(prev_conc_old) && !identical(prev_conc_old, as.character(pick_row$Concourse))) {
                last_change_time[i] <- as.integer(pick_row$DepMin)
              }
              last_conc[i]  <- as.character(pick_row$Concourse)
              last_S[i]     <- as.integer(assignable)
              debug_note(d, i, "commit",
                         list(
                           urn = as.integer(pick_row$`Unique Route Number`),
                           dep = as.integer(pick_row$DepMin),
                           assigned = as.integer(assignable),
                           cap_left = as.integer(cap_left[[d]])
                         ))
              end_time_comp[i] <- max(end_time_comp[i], as.integer(pick_row$DepMin) + as.integer(10 * ceiling(as.integer(assignable)/2)))
              
              # Only warn here when Hard Hours is OFF; if ON, we enforced above
              span_min <- if (is.finite(max_time[i]) && is.finite(first_time[i])) max_time[i] - first_time[i] else 0L
              if (!isTRUE(hard_hours_flags[i]) &&
                  is.finite(cap_min_ii) &&
                  span_min > cap_min_ii) {
                slot_tag <- paste0(d, " (", i, ")")
                bypass_acc_loc$daily_hours_days <- sort(unique(c(bypass_acc_loc$daily_hours_days %||% character(0), slot_tag)))
              }
              
              # SAFE: build/resize the used mask for slot i if needed; mark this specific candidate as used globally
              cur_used <- if (i <= length(used_idx) && length(used_idx[[i]])) {
                used_idx[[i]]
              } else {
                nr <- tryCatch(nrow(day_cands[[i]]), error = function(e) 0L)
                rep(FALSE, if (is.finite(nr) && nr > 0L) nr else 0L)
              }
              local_mask <- which(!cur_used)
              if (length(local_mask) >= pick_idx) {
                cur_used[local_mask[pick_idx]] <- TRUE
                used_idx[[i]] <- cur_used
              }
              # success; leave the local loop
              break
            } else {
              # REFUSE COMMIT: mark this candidate as used for THIS slot and try the next best on the same day
              cur_used <- if (i <= length(used_idx) && length(used_idx[[i]])) {
                used_idx[[i]]
              } else {
                nr <- tryCatch(nrow(day_cands[[i]]), error = function(e) 0L)
                rep(FALSE, if (is.finite(nr) && nr > 0L) nr else 0L)
              }
              local_mask <- which(!cur_used)
              if (length(local_mask) >= pick_idx) {
                cur_used[local_mask[pick_idx]] <- TRUE
                used_idx[[i]] <- cur_used
              }
              debug_note(d, i, "retry_next_on_day",
                         list(
                           urn = as.integer(pick_row$`Unique Route Number`),
                           dep = as.integer(pick_row$DepMin)
                         ))
              # knock out this candidate and continue locally
              loc_score[pick_idx] <- -Inf
              # continue repeat to try the next-best for this day
            }
          } # end repeat local day tries
          
          # no-progress escape: if we made no commit this iteration, stop after 2 scans
          if (isTRUE(did_commit)) {
            stall_scans <- 0L
          } else {
            stall_scans <- stall_scans + 1L
          }
          if (stall_scans >= 2L) break
          if (!any(cap_left > 0L)) break
        } # repeat
        
        for (i in seq_along(days)) {
          if (is.data.frame(assignments[[i]]) && nrow(assignments[[i]])) {
            assignments[[i]] <- assignments[[i]] %>%
              dplyr::arrange(DepMin, Concourse, Airline) %>%
              dplyr::select(Day, Airline, Concourse, Gate, Destination, `Flight #`,
                            `Departure Time`, `Assigned Surveys`, `Flight Type`, `Airline Code`,
                            `Unique Route Number`, DepMin, `Destination Code`)
          } else assignments[[i]] <- tibble::tibble()
        }
        
        list(
          assignments = assignments,
          route_remaining = route_remaining_local,
          bypass = bypass_acc_loc,
          live_bins = live_bins_loc,
          ampm_left = ampm_left,
          anchor_dates = anchor_dates
        )
      }
      
      # Run several randomized tries and keep the best total
      N_TRIES <-3L
      BEST <- NULL; BEST_TOTAL <- -Inf
      
      for (try in seq_len(N_TRIES)) {
        res <- suppressWarnings(run_global_once(jitter_sd = 0.08, seed = sample.int(.Machine$integer.max, 1)))
        tot <- sum(vapply(res$assignments, function(df) if (is.data.frame(df) && nrow(df)) sum(df$`Assigned Surveys`) else 0L, integer(1)))
        if (tot > BEST_TOTAL) { BEST_TOTAL <- tot; BEST <- res }
      }
      
      assignments <- BEST$assignments
      route_remaining <- BEST$route_remaining
      bypass_acc <- BEST$bypass
      live_bins <- BEST$live_bins
      ampm_left <- BEST$ampm_left
      anchor_dates <- BEST$anchor_dates
      # ---- END GLOBAL INTERLEAVED SCHEDULER --------------------------------
      # ---- FINAL HARD-CONSTRAINTS FILLER (iterative) -------------------------
      # Purpose: if a slot still has room and there is no concrete day-level blocker,
      # pack up to the per-flight cap while honoring spacing_after(), day caps, bin caps, and latest/earliest.
      if (as.integer(input$month_index) %in% c(1L, 2L)) {
        max_fill_passes <- 3L
        day_to_suffix <- c(Mon="mon", Tue="tue", Wed="wed", Thu="thu", Fri="fri", Sat="sat", Sun="sun")
        earliest_min  <- parse_user_time(input$earliest_dep)
        latest_min    <- parse_user_time(input$latest_dep)
        use_hard_earliest <- isTRUE(input$hard_earliest)
        use_hard_latest   <- ((as.integer(input$month_index) %in% c(1L,2L)) || isTRUE(input$hard_latest))
        per_f_cap <- as.integer(nzint(input$per_flight_cap %||% 10L))
        
        # helper: max surveys that fit before the next flight, given spacing_after tail
        max_fit_to_next <- function(gap_min, conc_switch) {
          bonus <- if (isTRUE(conc_switch)) 15L else 0L
          M <- as.integer(gap_min - bonus)
          if (M < 0L) return(0L)
          # spacing_after(S) = 10 * ceil(S/2) + bonus  ==> ceil(S/2) <= floor(M/10)
          as.integer(2L * floor(M / 10))
        }
        
        for (pass in seq_len(max_fill_passes)) {
          added_any <- FALSE
          
          # NEW: fill the emptiest slot(s) first each pass
          left_by_slot <- vapply(seq_along(days), function(ii) {
            sched_ii <- assignments[[ii]]
            used_ii  <- if (is.data.frame(sched_ii) && nrow(sched_ii)) {
              as.integer(sum(sched_ii$`Assigned Surveys`, na.rm = TRUE))
            } else 0L
            cap_ii   <- as.integer((day_caps[ii] %||% 40L))
            max(0L, cap_ii - used_ii)
          }, integer(1))
          
          ord_slots <- order(left_by_slot, decreasing = TRUE, na.last = TRUE)
          for (i in ord_slots) {
            slot_cap <- as.integer((day_caps[i] %||% 40L))
            used_now <- if (is.data.frame(assignments[[i]]) && nrow(assignments[[i]])) sum(assignments[[i]]$`Assigned Surveys`, na.rm = TRUE) else 0L
            left_day <- as.integer(slot_cap - used_now)
            if (left_day <= 0L) next
            
            d <- as.character(days[i])
            
            # Candidate pool for this day (respect optional date restrictions)
            cand <- df %>% dplyr::filter(Day == d)
            if (!nrow(cand)) next
            if (isTRUE(input$restrict_dates_master)) {
              slot_labels <- c(input$day1, input$day2, input$day3, input$day4)
              slot_idx    <- which(slot_labels %in% DAY_LEVELS)
              slot_no <- if (length(slot_idx) >= i) slot_idx[i] else NA_integer_
              allowed <- if (!is.na(slot_no)) (input[[paste0("dates_slot", slot_no)]] %||% character(0)) else character(0)
              if (length(allowed)) {
                cand <- cand[cand$dep_date %in% as.Date(allowed), , drop = FALSE]
                if (!nrow(cand)) next
              }
            }
            if (!("DepMin" %in% names(cand))) {
              cand$DepMin <- vapply(cand$`Departure Time`, parse_user_time, integer(1))
            }
            
            # respect latest/earliest if hard
            cand <- cand[(!use_hard_earliest | cand$DepMin >= earliest_min) &
                           (!use_hard_latest   | cand$DepMin <= latest_min), , drop = FALSE]
            if (!nrow(cand)) next
            # Rolling max-hours feasibility band (do NOT clamp to a pre-chosen window)
            hh_flags <- state$hard_hours_flags %||% NULL
            hh_on <- if (!is.null(hh_flags) && length(hh_flags) >= i) {
              isTRUE(hh_flags[[i]])
            } else {
              as.integer(input$month_index) %in% c(1L, 2L)
            }
            
            if (isTRUE(hh_on)) {
              cap_hours_i <- if (isTRUE(input$fine_tune_days)) nzint(input[[paste0("ft_hours_", i)]]) else nzint(input$max_hours)
              if (!is.finite(cap_hours_i) || cap_hours_i <= 0L) cap_hours_i <- 6L
              cap_min_i <- as.integer(cap_hours_i) * 60L
              
              # Current earliest/latest in this slot (from what is already scheduled)
              sched_i <- assignments[[i]]
              if (is.data.frame(sched_i) && nrow(sched_i)) {
                cur_min <- suppressWarnings(as.integer(min(as.integer(sched_i$DepMin), na.rm = TRUE)))
                cur_max <- suppressWarnings(as.integer(max(as.integer(sched_i$DepMin), na.rm = TRUE)))
              } else {
                cur_min <- NA_integer_
                cur_max <- NA_integer_
              }
              
              # If we already have something scheduled, clamp candidates to the rolling band:
              # allow_min = cur_max - cap, allow_max = cur_min + cap
              if (is.finite(cur_min) && is.finite(cur_max)) {
                allow_min <- as.integer(cur_max - cap_min_i)
                allow_max <- as.integer(cur_min + cap_min_i)
                
                if (isTRUE(use_hard_earliest) && is.finite(earliest_min)) allow_min <- max(allow_min, as.integer(earliest_min))
                if (isTRUE(use_hard_latest)   && is.finite(latest_min))   allow_max <- min(allow_max, as.integer(latest_min))
                
                cand <- cand[cand$DepMin >= allow_min & cand$DepMin <= allow_max, , drop = FALSE]
                if (!nrow(cand)) next
              }
              # If nothing is scheduled yet, do NOT clamp here; first pick can be anywhere inside hard earliest/latest.
            }
            
            # build preview with a synthetic candidate row and compute max pack S that still fits next gap
            sched_i <- assignments[[i]]; if (!is.data.frame(sched_i)) sched_i <- tibble::tibble()
            if (nrow(sched_i)) sched_i <- dplyr::arrange(sched_i, DepMin)
            
            # iterate routes in decreasing remaining need so we finish routes when possible
            cand$rem_left <- route_remaining$remaining[match(cand$`Unique Route Number`,
                                                             route_remaining$`Unique Route Number`)]
            cand <- cand[order(-as.integer(cand$rem_left %||% 0L)), , drop = FALSE]
            
            for (k in seq_len(nrow(cand))) {
              if (left_day <= 0L) break
              
              pick <- cand[k, , drop = FALSE]
              urn  <- as.integer(pick$`Unique Route Number`)
              # Remaining need on this URN (read from the up-to-date global book)
              rem <- as.integer(route_remaining$remaining[match(urn, route_remaining$`Unique Route Number`)] %||% 0L)
              if (rem <= 0L) next
              
              # per-flight cap and day-left
              S_cap <- min(per_f_cap, rem, left_day)
              
              # where would it insert?
              dep_try <- as.integer(pick$DepMin)
              conc_try <- cclean(pick$Concourse)
              preview <- if (!nrow(sched_i)) pick else dplyr::bind_rows(sched_i, pick) %>% dplyr::arrange(DepMin)
              pos <- which(preview$DepMin == dep_try)[1]
              depv <- as.integer(preview$DepMin); concv <- cclean(preview$Concourse)
              
              # spacing to prev/next to compute max S that fits to the right
              gap_next <- if (length(depv) > pos) as.integer(depv[pos+1] - depv[pos]) else Inf
              switch_next <- if (length(depv) > pos) (concv[pos] != concv[pos+1]) else FALSE
              S_fit_next <- if (is.finite(gap_next)) max_fit_to_next(gap_next, switch_next) else S_cap
              
              # also respect spacing to the *previous* neighbor (its tail already set by its Assigned Surveys)
              ok_prev <- TRUE
              if (pos > 1) {
                need_prev <- spacing_after(as.integer(preview$`Assigned Surveys`[pos-1] %||% 0L),
                                           concv[pos-1] != concv[pos])
                ok_prev <- as.integer(depv[pos]) >= as.integer(depv[pos-1] + need_prev)
              }
              if (!ok_prev) next
              
              # Respect AM/PM room remaining for this slot (Months 1–2)
              room_ampm2 <- 1e9L
              if (month %in% c(1,2)) {
                if (!isTRUE(am_controls$split)) {
                  room_ampm2 <- as.integer(if (dep_try < 12L*60L) (ampm_left$AM %||% 0L) else (ampm_left$PM %||% 0L))
                } else {
                  if (is_weekend(d)) {
                    room_ampm2 <- as.integer(if (dep_try < 12L*60L) (ampm_left$AM_we %||% 0L) else (ampm_left$PM_we %||% 0L))
                  } else {
                    room_ampm2 <- as.integer(if (dep_try < 12L*60L) (ampm_left$AM_wk %||% 0L) else (ampm_left$PM_wk %||% 0L))
                  }
                }
              }
              assignable <- as.integer(max(0L, min(S_cap, S_fit_next, room_ampm2)))
              if (assignable < 1L) next
              
              out_row <- pick
              out_row$`Assigned Surveys` <- as.integer(assignable)
              assignments[[i]] <- dplyr::bind_rows(sched_i, out_row) %>% dplyr::arrange(DepMin)
              # Decrement AM/PM pool for the filler addition
              if (month %in% c(1,2)) {
                if (!isTRUE(am_controls$split)) {
                  if (dep_try < 12L*60L) {
                    ampm_left$AM <- max(0L, (ampm_left$AM %||% 0L) - assignable)
                  } else {
                    ampm_left$PM <- max(0L, (ampm_left$PM %||% 0L) - assignable)
                  }
                } else {
                  if (is_weekend(d)) {
                    if (dep_try < 12L*60L) {
                      ampm_left$AM_we <- max(0L, (ampm_left$AM_we %||% 0L) - assignable)
                    } else {
                      ampm_left$PM_we <- max(0L, (ampm_left$PM_we %||% 0L) - assignable)
                    }
                  } else {
                    if (dep_try < 12L*60L) {
                      ampm_left$AM_wk <- max(0L, (ampm_left$AM_wk %||% 0L) - assignable)
                    } else {
                      ampm_left$PM_wk <- max(0L, (ampm_left$PM_wk %||% 0L) - assignable)
                    }
                  }
                }
              }
              
              # update book-keeping
              ridx <- match(urn, route_remaining$`Unique Route Number`)
              if (!is.na(ridx)) route_remaining$remaining[ridx] <- pmax(0L, as.integer(route_remaining$remaining[ridx]) - assignable)
              left_day <- left_day - assignable
              sched_i <- assignments[[i]]
              added_any <- TRUE
            }
          }
          
          if (!isTRUE(added_any)) break
        }
      }
      # ---- END FINAL HARD-CONSTRAINTS FILLER ---------------------------------
      
      # ---- Date Fit Summary + Auto-Repair (enforce at least one usable date per slot) ----
      fit_rows <- list()
      slot_dates <- vector("list", length(days))
      datefit_repairs <- list()   # for yellow-box messaging
      # Map each logical schedule slot (i) back to the original Day 1–4 selector
      slot_labels <- c(input$day1, input$day2, input$day3, input$day4)
      slot_idx    <- which(slot_labels %in% DAY_LEVELS)
      # Now days[i] == slot_labels[slot_idx[i]] for all i
      
      for (i in seq_along(days)) {
        d <- days[i]
        sched_i <- assignments[[i]]
        dt_best <- as.Date(NA)
        if (!is.data.frame(sched_i) || !nrow(sched_i)) next
        
        all_dates <- df %>%
          dplyr::filter(Day == d) %>%
          dplyr::pull(dep_date) %>%
          unique() %>%
          sort()
        
        # Respect "Specify which dates..." if set, slot-by-slot
        allowed <- NULL
        if (isTRUE(input$restrict_dates_master)) {
          # Map this schedule slot i back to the original Day 1–4 index
          slot_pos <- slot_idx[i]
          
          if (length(slot_pos) == 1L && is.finite(slot_pos)) {
            slot_input_id <- paste0("dates_slot", slot_pos)
            allowed <- as.Date(input[[slot_input_id]] %||% character(0))
          } else {
            allowed <- character(0)
          }
        }
        if (!is.null(allowed)) {
          all_dates <- intersect(all_dates, allowed)
        }
        
        # Keys we require to co-exist on a single date
        need_keys_full <- sched_i %>% dplyr::distinct(`Airline Code`,`Destination Code`,`Flight #`, Airline, Destination)
        use_codes <- !all(is.na(need_keys_full$`Airline Code`)) && !all(is.na(need_keys_full$`Destination Code`))
        by_keys <- if (use_codes) c("Airline Code","Destination Code","Flight #") else c("Airline","Destination","Flight #")
        need_keys <- need_keys_full %>% dplyr::select(dplyr::all_of(by_keys)) %>% dplyr::distinct()
        
        usable_flags <- logical(length(all_dates))
        coverage     <- integer(length(all_dates))
        
        for (j in seq_along(all_dates)) {
          dt <- all_dates[j]
          have <- df %>%
            dplyr::filter(Day == d, dep_date == dt) %>%
            dplyr::select(dplyr::all_of(by_keys)) %>%
            dplyr::distinct()
          
          # Usable if *all* needed flights exist that same date
          usable_flags[j] <- (nrow(dplyr::semi_join(need_keys, have, by = by_keys)) == nrow(need_keys))
          
          # Coverage = how many of the scheduled flights exist that date (for best-date fallback)
          coverage[j] <- nrow(dplyr::semi_join(need_keys, have, by = by_keys))
        }
        
        usable_dates   <- all_dates[usable_flags]
        unusable_dates <- setdiff(all_dates, usable_dates)
        
        if (!length(usable_dates)) {
          # No single date had all flights. Do NOT prune rows.
          # Enforce the per-day anchor so each built schedule has ≥1 realizable date.
          ad <- anchor_dates[[d]] %||% as.Date(NA)
          if (isTRUE(is.finite(suppressWarnings(as.numeric(ad))))) {
            slot_dates[[i]] <- as.Date(ad)
            usable_dates    <- as.Date(ad)
            unusable_dates  <- setdiff(all_dates, usable_dates)
            # No yellow "pruned" message; we built on the anchor date already.
          } else {
            # No candidate dates at all for this weekday—drop the slot’s schedule.
            if (nrow(sched_i)) {
              datefit_repairs[[length(datefit_repairs)+1L]] <- sprintf(
                "Date-fit repair: removed %d survey(s) from %s (%s) because no %s dates were available.",
                sum(sched_i$`Assigned Surveys`, na.rm = TRUE),
                d, i, d
              )
            }
            assignments[[i]] <- sched_i[0, , drop = FALSE]
          }
        }
        
        if (is.null(slot_dates[[i]]) || is.na(slot_dates[[i]])) {
          if (length(usable_dates) > 0) {
            slot_dates[[i]] <- as.Date(min(usable_dates))
          } else if (isTRUE(is.finite(suppressWarnings(as.numeric(dt_best))))) {
            slot_dates[[i]] <- as.Date(dt_best)
          } else {
            slot_dates[[i]] <- as.Date(NA)
          }
        }
        fit_rows[[length(fit_rows)+1L]] <- tibble::tibble(
          Day = d,
          `Usable Dates`   = if (length(usable_dates))   paste(vapply(usable_dates, fmt_md, character(1)), collapse = ", ") else "",
          `Unusable Dates` = if (length(unusable_dates)) paste(vapply(unusable_dates, fmt_md, character(1)), collapse = ", ") else ""
        )
      }
      
      fit_df <- {
        if (length(fit_rows)) {
          dplyr::bind_rows(fit_rows)
        } else {
          tibble::tibble(
            Day = character(0),
            `Usable Dates` = character(0),
            `Unusable Dates` = character(0)
          )
        }
      } %>%
        dplyr::mutate(Day = factor(.data$Day, levels = DAY_LEVELS)) %>%
        dplyr::arrange(.data$Day)
      state$date_fit <- fit_df
      state$slot_date <- slot_dates
      
      # Stash messages for yellow box (picked up later)
      state$datefit_repairs <- unique(unlist(datefit_repairs, use.names = FALSE))
      
      # ---- Rebalance passes (iterate up to 3x, stop when no change) --------
      prelim_remaining <- route_remaining %>% dplyr::filter(remaining > 0) %>% dplyr::pull(`Unique Route Number`)
      if (length(prelim_remaining)) {
        for (rb_iter in 1:3) {
          before_tot <- sum(vapply(assignments, function(df) if (is.data.frame(df) && nrow(df)) sum(df$`Assigned Surveys`) else 0L, integer(1)))
          new_assign <- try_rebalance(days, assignments, df_all = df, day_caps = day_caps, controls = controls, month = month, bin_caps = bin_caps)
          after_tot <- sum(vapply(new_assign, function(df) if (is.data.frame(df) && nrow(df)) sum(df$`Assigned Surveys`) else 0L, integer(1)))
          assignments <- new_assign
          if (!is.finite(before_tot) || !is.finite(after_tot) || after_tot <= before_tot) break
        }
      }
      
      # --- Month-3 BIN PRESSURE RELIEF (AM focus) ---------------------------------
      # Free up Weekend AM capacity by moving a scheduled weekend-AM route to a weekday-AM
      # occurrence of the *same* route when that occurrence exists and has room.
      if (month == 3) {
        # 1) Collect unscheduled messages that explicitly hit the "Weekend AM" bin cap
        blocked_urns <- integer(0)
        unsched_msgs <- state$unscheduled_reasons %||% character(0)
        if (length(unsched_msgs)) {
          pat <- "exceed the maximum desired Weekend AM assigned surveys"
          urns <- gsub("^.*?Route\\s+(\\d+)\\s+cannot.*$", "\\1", unsched_msgs[grepl(pat, unsched_msgs)])
          urns <- suppressWarnings(as.integer(urns[is.finite(as.numeric(urns))]))
          blocked_urns <- unique(urns)
        }
        
        if (length(blocked_urns)) {
          # Helpers
          is_am   <- function(depmin) { depmin < parse_user_time("12:00 PM") }
          is_we   <- function(day)    { day %in% c("Sat", "Sun") }
          is_wd   <- function(day)    { !is_we(day) }
          
          # Current bin counts
          count_in_bin <- function(assigns, day_filter, am_flag) {
            total <- 0L
            for (k in seq_along(assigns)) {
              dfk <- assigns[[k]]
              if (!is.data.frame(dfk) || !nrow(dfk)) next
              dname <- as.character(days[k])
              if (!day_filter(dname)) next
              if (!any(dfk$DepMin >= 0)) next
              rows <- dfk[is_am(dfk$DepMin) == am_flag, , drop = FALSE]
              if (!nrow(rows)) next
              total <- total + sum(rows$`Assigned Surveys`, na.rm = TRUE)
            }
            total
          }
          
          wd_am_cap <- as.integer(nzint(input$wd_am) %||% 0L)
          we_am_cap <- as.integer(nzint(input$we_am) %||% 0L)
          
          # Only try when Weekend AM is at/over cap and Weekday AM still has room
          we_am_used <- count_in_bin(assignments, is_we, TRUE)
          wd_am_used <- count_in_bin(assignments, is_wd, TRUE)
          
          if (is.finite(we_am_cap) && is.finite(wd_am_cap) &&
              we_am_used >= we_am_cap && wd_am_used < wd_am_cap) {
            
            # For each blocked URN, try to make exactly 1 slot of room
            for (urn in blocked_urns) {
              made_room <- FALSE
              
              # 2) Find a donor row currently scheduled on Weekend AM (any route, but prefer routes with weekday AM occurrence)
              donor <- NULL
              donor_i <- NA_integer_
              for (i_slot in seq_along(days)) {
                dname <- as.character(days[i_slot])
                if (!is_we(dname)) next
                df_i <- assignments[[i_slot]]
                if (!is.data.frame(df_i) || !nrow(df_i)) next
                # AM rows in this weekend slot
                am_rows <- which(is_am(df_i$DepMin))
                if (!length(am_rows)) next
                
                # Rank donors: prefer routes that have weekday AM occurrences in df_all
                for (ri in am_rows) {
                  urn_d <- as.integer(df_i$`Unique Route Number`[ri])
                  # Skip if this is the same urn we're trying to insert; moving itself won't help
                  if (isTRUE(urn_d == urn)) next
                  
                  weekday_alts <- df %>%
                    dplyr::filter(`Unique Route Number` == urn_d, Day %in% c("Mon","Tue","Wed","Thu","Fri")) %>%
                    dplyr::mutate(DepMin = as.integer(DepMin)) %>%
                    dplyr::filter(is_am(DepMin))
                  
                  if (nrow(weekday_alts)) {
                    donor <- df_i[ri, , drop = FALSE]
                    donor_i <- i_slot
                    break
                  }
                }
                if (!is.null(donor)) break
              }
              
              if (!is.null(donor) && is.finite(donor_i)) {
                urn_d <- as.integer(donor$`Unique Route Number`[1])
                
                # 3) Try to reschedule donor route to a weekday-AM occurrence where per-day cap and hard-hours allow it
                weekday_alts <- df %>%
                  dplyr::filter(`Unique Route Number` == urn_d, Day %in% c("Mon","Tue","Wed","Thu","Fri")) %>%
                  dplyr::mutate(DepMin = as.integer(DepMin)) %>%
                  dplyr::filter(is_am(DepMin)) %>%
                  dplyr::arrange(Day, DepMin)
                
                for (r in seq_len(nrow(weekday_alts))) {
                  alt <- weekday_alts[r, , drop = FALSE]
                  # Find target slot index for alt$Day
                  j <- which(days == as.character(alt$Day)[1])[1]
                  if (!is.finite(j) || is.na(j)) next
                  
                  # Per-day survey cap for that target slot
                  slot_cap_j  <- as.integer((day_caps[[days[j]]] %||% 40L))
                  used_j      <- if (is.data.frame(assignments[[j]]) && nrow(assignments[[j]]))
                    sum(assignments[[j]]$`Assigned Surveys`, na.rm = TRUE) else 0L
                  if (used_j >= slot_cap_j) next
                  
                  # Hard-hours pre-commit guard on target slot j
                  cap_min_j <- {
                    if (isTRUE(input$fine_tune_days)) {
                      v <- nzint(input[[paste0("ft_hours_", j)]])
                      if (!is.finite(v) || v <= 0L) 24L else v
                    } else {
                      v <- nzint(input$max_hours)
                      if (!is.finite(v) || v <= 0L) 6L else v
                    }
                  }
                  cap_min_j <- as.integer(pmax(1L, cap_min_j) * 60L)
                  # prospective span if we add alt into slot j
                  slot_depmins_j <- if (is.data.frame(assignments[[j]]) && nrow(assignments[[j]]))
                    as.integer(assignments[[j]]$DepMin) else integer(0)
                  t_first_j <- if (length(slot_depmins_j)) min(slot_depmins_j) else as.integer(alt$DepMin)
                  t_last_j  <- if (length(slot_depmins_j)) max(slot_depmins_j) else as.integer(alt$DepMin)
                  t_first_j <- min(t_first_j, as.integer(alt$DepMin))
                  t_last_j  <- max(t_last_j,  as.integer(alt$DepMin))
                  if (isTRUE(hard_hours_flags[j]) && is.finite(cap_min_j) && ((t_last_j - t_first_j) > cap_min_j)) next
                  
                  # 3a) Commit: remove donor from weekend slot and add weekday alt to target slot j
                  # Remove donor
                  df_d <- assignments[[donor_i]]
                  idx_rm <- which(df_d$`Unique Route Number` == urn_d & df_d$DepMin == donor$DepMin)[1]
                  if (!is.na(idx_rm)) {
                    assignments[[donor_i]] <- df_d[-idx_rm, , drop = FALSE]
                  }
                  
                  # Add target weekday occurrence row
                  add_row <- tibble::tibble(
                    Day = as.character(alt$Day),
                    Airline = as.character(alt$Airline %||% NA_character_),
                    Concourse = as.character(alt$Concourse),
                    Gate = as.character(alt$Gate %||% NA_character_),
                    Destination = as.character(alt$Destination %||% NA_character_),
                    `Flight #` = as.character(alt$`Flight #` %||% NA_character_),
                    `Departure Time` = as.character(alt$`Departure Time` %||% NA_character_),
                    `Assigned Surveys` = as.integer(donor$`Assigned Surveys`[1] %||% 0L),
                    `Flight Type` = as.character(alt$`Flight Type` %||% NA_character_),
                    `Airline Code` = as.character(alt$`Airline Code` %||% NA_character_),
                    `Unique Route Number` = as.integer(alt$`Unique Route Number`),
                    DepMin = as.integer(alt$DepMin),
                    `Destination Code` = as.character(alt$`Destination Code` %||% NA_character_)
                  )
                  assignments[[j]] <- dplyr::bind_rows(assignments[[j]] %||% tibble::tibble(), add_row) %>%
                    dplyr::arrange(DepMin, Concourse, Airline)
                  
                  made_room <- TRUE
                  break
                } # for weekday_alts
                
              } # found donor
              
              # 4) If room was made in Weekend AM, try to place the blocked URN on weekend AM now
              if (made_room) {
                sun_slots <- which(days == "Sun")
                # Look for Sunday 10:24 AM instance of this URN in df
                cand26 <- df %>%
                  dplyr::filter(`Unique Route Number` == urn, Day == "Sun") %>%
                  dplyr::mutate(DepMin = as.integer(DepMin)) %>%
                  dplyr::arrange(DepMin)
                if (nrow(cand26)) {
                  for (ii in sun_slots) {
                    # Compute a per-slot target index with concourse preference when under 90% of the cap
                    slot_cap_ii <- as.integer((day_caps[ii] %||% 40L))
                    used_ii <- if (is.data.frame(assignments[[ii]]) && nrow(assignments[[ii]]))
                      sum(assignments[[ii]]$`Assigned Surveys`, na.rm = TRUE) else 0L
                    
                    # Base choice: AM flight nearest to 10:24 AM
                    target_r_all <- as.integer(cand26$DepMin)
                    base_idx <- which.min(abs(target_r_all - as.integer(parse_user_time("10:24 AM"))))
                    
                    # If under 90% filled, prefer same concourse as the nearest scheduled neighbor (reduce 30-min walks)
                    if (used_ii < ceiling(0.9 * slot_cap_ii) && is.data.frame(assignments[[ii]]) && nrow(assignments[[ii]])) {
                      dep_i  <- as.integer(assignments[[ii]]$DepMin)
                      conc_i <- cclean(assignments[[ii]]$Concourse)
                      nearest <- if (length(dep_i)) which.min(abs(dep_i - target_r_all[base_idx])) else NA_integer_
                      ref_conc <- if (is.finite(nearest)) conc_i[nearest] else NA_character_
                      same <- which(cclean(cand26$Concourse) == ref_conc)
                      if (length(same)) {
                        # Among same-concourse candidates, still aim near 10:24
                        base_idx <- same[which.min(abs(as.integer(cand26$DepMin[same]) - as.integer(parse_user_time("10:24 AM"))))]
                      }
                    }
                    target_idx <- base_idx
                    slot_dep <- as.integer(cand26$DepMin[target_idx])
                    # check bin: we are adding AM; ensure weekend AM now has room (recompute simple count)
                    used_we_am <- count_in_bin(assignments, is_we, TRUE)
                    if (used_we_am >= we_am_cap) break
                    # pre-commit hard-hours for this slot
                    cap_min_ii <- {
                      if (isTRUE(input$fine_tune_days)) {
                        v <- nzint(input[[paste0("ft_hours_", ii)]])
                        if (!is.finite(v) || v <= 0L) 24L else v
                      } else {
                        v <- nzint(input$max_hours)
                        if (!is.finite(v) || v <= 0L) 6L else v
                      }
                    }
                    cap_min_ii <- as.integer(pmax(1L, cap_min_ii) * 60L)
                    slot_depmins <- if (is.data.frame(assignments[[ii]]) && nrow(assignments[[ii]]))
                      as.integer(assignments[[ii]]$DepMin) else integer(0)
                    t_first <- if (length(slot_depmins)) min(slot_depmins) else slot_dep
                    t_last  <- if (length(slot_depmins)) max(slot_depmins) else slot_dep
                    t_first <- min(t_first, slot_dep)
                    t_last  <- max(t_last,  slot_dep)
                    if (isTRUE(hard_hours_flags[ii]) && is.finite(cap_min_ii) && ((t_last - t_first) > cap_min_ii)) next
                    
                    # per-day slot cap
                    slot_cap_ii <- as.integer((day_caps[ii] %||% 40L))
                    used_ii <- if (is.data.frame(assignments[[ii]]) && nrow(assignments[[ii]]))
                      sum(assignments[[ii]]$`Assigned Surveys`, na.rm = TRUE) else 0L
                    if (used_ii >= slot_cap_ii) next
                    if (used_ii >= ceiling(0.9 * slot_cap_ii)) next  # only sprinkle when <90% of day cap
                    
                    # Amount to add: never 1 unless URN has only 1 left; otherwise 2–3 within caps
                    base_rem <- {
                      idx_urn <- match(urn, route_base$`Unique Route Number`)
                      if (is.finite(idx_urn)) as.integer(route_base$remaining[idx_urn]) else 0L
                    }
                    cur_assigned_urn <- sum(vapply(assignments, function(df) {
                      if (is.data.frame(df) && nrow(df)) {
                        sum(df$`Assigned Surveys`[as.integer(df$`Unique Route Number`) == as.integer(urn)], na.rm = TRUE)
                      } else 0L
                    }, integer(1)))
                    rem_now <- max(0L, base_rem - cur_assigned_urn)
                    cap_left_ii <- max(0L, slot_cap_ii - used_ii)
                    add_n <- if (rem_now <= 1L) 1L else as.integer(max(2L, min(3L, rem_now, cap_left_ii)))
                    if (add_n <= 0L) next
                    # Month-3 bin-cap guard for pressure-relief sprinkle
                    if (month == 3 && !is.null(bin_caps)) {
                      bname26 <- flight_bin(as.character(days[ii]), as.integer(cand26$DepMin[target_idx]))
                      if (is.character(bname26) && nzchar(bname26) &&
                          !is.null(bin_caps[[bname26]]) && is.finite(as.numeric(bin_caps[[bname26]]))) {
                        used26 <- as.integer(live_bins_loc[[bname26]] %||% 0L)
                        cap26  <- as.integer(bin_caps[[bname26]] %||% 0L)
                        room26 <- pmax(0L, cap26 - used26)
                        if (room26 <= 0L) next
                        if (add_n > room26) add_n <- as.integer(room26)
                      }
                    }
                    # commit add for urn
                    add26 <- tibble::tibble(
                      Day = as.character(days[ii]),
                      Airline = as.character(cand26$Airline[target_idx] %||% NA_character_),
                      Concourse = as.character(cand26$Concourse[target_idx]),
                      Gate = as.character(cand26$Gate[target_idx] %||% NA_character_),
                      Destination = as.character(cand26$Destination[target_idx] %||% NA_character_),
                      `Flight #` = as.character(cand26$`Flight #`[target_idx] %||% NA_character_),
                      `Departure Time` = as.character(cand26$`Departure Time`[target_idx] %||% NA_character_),
                      `Assigned Surveys` = as.integer(add_n),
                      `Flight Type` = as.character(cand26$`Flight Type`[target_idx] %||% NA_character_),
                      `Airline Code` = as.character(cand26$`Airline Code`[target_idx] %||% NA_character_),
                      `Unique Route Number` = as.integer(cand26$`Unique Route Number`[target_idx]),
                      DepMin = as.integer(cand26$DepMin[target_idx]),
                      `Destination Code` = as.character(cand26$`Destination Code`[target_idx] %||% NA_character_)
                    )
                    assignments[[ii]] <- dplyr::bind_rows(assignments[[ii]] %||% tibble::tibble(), add26) %>%
                      dplyr::arrange(DepMin, Concourse, Airline)
                    if (month == 3) {
                      bname26_upd <- flight_bin(as.character(days[ii]), as.integer(cand26$DepMin[target_idx]))
                      if (is.character(bname26_upd) && nzchar(bname26_upd)) {
                        live_bins_loc[[bname26_upd]] <- as.integer(live_bins_loc[[bname26_upd]] %||% 0L) + as.integer(add_n)
                      }
                    }
                    break
                  }
                }
              } # made_room
            } # for urn
          } # weekend AM at cap and weekday AM has room
        } # length(blocked_urns)
      }
      # --- End BIN PRESSURE RELIEF --------------------------------------------
      # Final hard enforcement of interflight spacing in Months 1–2 (prune any residual violations)
      prune_slot_spacing <- function(df) {
        if (!is.data.frame(df) || !nrow(df)) return(df)
        df <- df[order(as.integer(df$DepMin)), , drop = FALSE]
        keep <- rep(FALSE, nrow(df))
        last_dep  <- -Inf
        last_conc <- NA_character_
        last_S    <- 0L
        for (k in seq_len(nrow(df))) {
          dep_k  <- as.integer(df$DepMin[k])
          conc_k <- cclean(df$Concourse[k])
          need_k <- spacing_after(as.integer(last_S), !identical(conc_k, last_conc))
          if (is.infinite(last_dep) || dep_k >= (last_dep + as.integer(need_k))) {
            keep[k]  <- TRUE
            last_dep <- dep_k
            last_conc <- conc_k
            last_S   <- as.integer(df$`Assigned Surveys`[k])
          }
        }
        df[keep, , drop = FALSE]
      }
      if (month %in% c(1L, 2L)) {
        assignments <- lapply(assignments, prune_slot_spacing)
      }
      
      # Recompute remaining after assignments
      assigned_long <- if (length(assignments)) dplyr::bind_rows(assignments) else tibble::tibble()
      if (!nrow(assigned_long)) assigned_long <- tibble::tibble(
        Day=character(0), Airline=character(0), Concourse=character(0), Gate=character(0),
        Destination=character(0), `Flight #`=character(0), `Departure Time`=character(0),
        `Assigned Surveys`=integer(0), `Flight Type`=character(0),
        `Airline Code`=character(0), `Destination Code`=character(0),
        `Unique Route Number`=integer(0), DepMin=integer(0)
      )
      
      # decrease remaining
      dec <- if (nrow(assigned_long)) {
        assigned_long %>% 
          group_by(`Unique Route Number`) %>% 
          summarise(dec = sum(`Assigned Surveys`), .groups = "drop")
      } else {
        tibble(`Unique Route Number` = integer(0), dec = integer(0))
      }
      
      route_updated <- route_base %>% 
        left_join(dec, by = "Unique Route Number") %>%
        mutate(
          dec = tidyr::replace_na(dec, 0L),
          remaining = pmax(0L, remaining - dec)
        )
      
      # Prefer codes/days from the "Routes Remaining" sheet
      codes_from_rr <- rr %>% 
        select(`Unique Route Number`, `Airline Code`, `Destination Code`, `Flight Type`, `Days of Operation`) %>% 
        distinct()
      
      # Only show rows that STILL need surveys (> 0). If none remain, this becomes a 0-row table.
      routes_updated <- route_updated %>%
        filter(remaining > 0L) %>%                                    # <— the key filter
        select(
          `Unique Route Number`,
          Airline,
          Destination,
          `Assigned Surveys` = remaining
        ) %>%
        left_join(codes_from_rr, by = "Unique Route Number") %>%
        arrange(`Unique Route Number`)
      
      # ---- Diagnostics (specific reasons) ----
      # Build reasons ONLY for routes that still have remaining > 0 in "Updated Routes Remaining"
      bins_now <- classify_bins(assigned_long, earliest_cap_min = parse_user_time(input$earliest_dep %||% "6:00 AM"), latest_cap_min = state$latest_cap_min)
      
      # Helpers for readable labels
      slot_label <- function(i) paste0(days[i], " (", i, ")")
      nice_bin <- function(b)
        switch(b, "wd_am"="Weekday AM", "wd_pm"="Weekday PM", "we_am"="Weekend AM", "we_pm"="Weekend PM", "(bin)")
      
      latest_cap_min <- state$latest_cap_min
      latest_cap <- suppressWarnings(
        as.integer(latest_cap_min %||% parse_user_time(input$latest_dep %||% "8:45 PM"))
      )
      hard_latest_applies <- isTRUE(input$hard_latest)
      earliest_cap_min <- state$earliest_cap_min
      earliest_cap <- suppressWarnings(
        as.integer(earliest_cap_min %||% parse_user_time(input$earliest_dep %||% "5:00 AM"))
      )
      hard_earliest_applies <- isTRUE(input$hard_earliest)
      # --- Locals needed by Diagnostics -----------------------------------------
      # (1) Reconstruct per-slot hours cap the same way as in planning
      day_hours_caps <- vapply(seq_along(days), function(i) {
        if (isTRUE(input$fine_tune_days)) {
          v <- nzint(input[[paste0("ft_hours_", i)]])
          if (!is.finite(v) || v <= 0L) 24L else v
        } else {
          v <- nzint(input$max_hours)
          if (!is.finite(v) || v <= 0L) 6L else v
        }
      }, integer(1))
      
      # (2) Surface any pre-planned windows saved during planning (may be empty)
      slot_windows <- state$slot_windows %||% list()
      
      # Per-slot caps & usage (handle duplicate weekdays) — use the fresh 'assignments'
      per_slot_totals <- vapply(seq_along(days), function(i) {
        x <- if (i >= 1L && i <= length(assignments)) assignments[[i]] else NULL
        if (is.data.frame(x) && nrow(x)) as.integer(sum(nzint(x$`Assigned Surveys`), na.rm = TRUE)) else 0L
      }, integer(1))
      per_slot_caps <- as.integer(day_caps)
      per_slot_full <- is.finite(per_slot_totals) & (per_slot_totals >= per_slot_caps)
      per_slot_full[is.na(per_slot_full)] <- FALSE
      
      # Per-slot hours windows (for slots with Hard Hours = TRUE):
      # - Use planned window start when present
      # - Else anchor at earliest scheduled departure for this slot
      # - Then clamp to hard earliest/latest caps (shortening the window if needed)
      slot_win <- vector("list", length(days))
      planned_win <- state$slot_windows %||% vector("list", length(days))
      
      get_depmin_vec_dbg <- function(df0) {
        if (!is.data.frame(df0) || !nrow(df0)) return(integer(0))
        if ("DepMin2" %in% names(df0)) return(as.integer(df0$DepMin2))
        if ("DepMin"  %in% names(df0)) return(as.integer(df0$DepMin))
        if ("Departure Time" %in% names(df0)) return(vapply(df0$`Departure Time`, parse_user_time, integer(1)))
        integer(0)
      }
      
      for (i in seq_along(days)) {
        if (!isTRUE(hard_hours_flags[i])) { slot_win[[i]] <- NULL; next }
        
        cap_hours_i <- as.integer(pmax(1L, nzint(day_hours_caps[i] %||% nzint(input$max_hours) %||% 6L)))
        cap_min_i   <- as.integer(cap_hours_i * 60L)
        
        # Start from planned window start if present; else earliest scheduled dep in this slot
        start_i <- NA_integer_
        if (length(planned_win) >= i && length(planned_win[[i]])) {
          start_i <- as.integer(planned_win[[i]]$start %||% NA_integer_)
        }
        if (!is.finite(start_i)) {
          depv <- get_depmin_vec_dbg(if (i >= 1L && i <= length(assignments)) assignments[[i]] else NULL)
          start_i <- suppressWarnings(as.integer(min(depv, na.rm = TRUE)))
        }
        
        if (is.finite(start_i)) {
          # Clamp start to hard earliest cap (if enabled)
          if (isTRUE(input$hard_earliest) && is.finite(earliest_cap)) {
            start_i <- as.integer(max(start_i, as.integer(earliest_cap)))
          }
          
          end_i <- as.integer(start_i + cap_min_i)
          
          # Clamp end to hard latest cap (if enabled)
          if (isTRUE(input$hard_latest) && is.finite(latest_cap)) {
            end_i <- as.integer(min(end_i, as.integer(latest_cap)))
          }
          
          slot_win[[i]] <- list(start = as.integer(start_i), end = as.integer(end_i))
        } else {
          slot_win[[i]] <- list(start = NA_integer_, end = NA_integer_)
        }
      }
      
      # Month 3 bin caps “room” snapshot
      wk_present_all <- any(vapply(days, is_weekend, logical(1)))
      bin_caps_now <- if (month == 3) list(
        wd_am = nzint(input$m3_wd_am), wd_pm = nzint(input$m3_wd_pm),
        we_am = if (wk_present_all) nzint(input$m3_we_am) else 0L,
        we_pm = if (wk_present_all) nzint(input$m3_we_pm) else 0L
      ) else NULL
      bin_room_left <- function(name) {
        if (is.null(bin_caps_now) || is.null(bin_caps_now[[name]]) || !is.finite(as.numeric(bin_caps_now[[name]]))) return(Inf)
        cap <- as.integer(bin_caps_now[[name]] %||% 0L)
        used <- as.integer(bins_now[[name]] %||% 0L)
        pmax(0L, cap - used)
      }
      
      # Only examine routes that still need surveys in Updated Routes Remaining
      routes_updated_nonzero <- routes_updated %>%
        dplyr::filter(`Assigned Surveys` > 0) %>%
        dplyr::select(`Unique Route Number`) %>%
        dplyr::distinct()
      
      unsched_msgs <- character(0)
      
      for (k in seq_len(nrow(routes_updated_nonzero))) {
        urn <- routes_updated_nonzero$`Unique Route Number`[k]
        reasons <- character(0)
        
        # All candidate flights for this URN across selected slots (before any filters)
        cand0 <- df %>% dplyr::filter(`Unique Route Number` == urn, Day %in% days)
        debug_note(
          day  = "ALL",
          slot = NA_integer_,
          step = "unsched_cand0",
          info = list(
            URN     = as.integer(urn),
            n_cand0 = nrow(cand0)
          )
        )
        if (!nrow(cand0)) {
          avail <- df %>% dplyr::filter(`Unique Route Number` == urn) %>% dplyr::distinct(Day) %>% dplyr::pull(Day)
          by_day_msgs <- vapply(days, function(d) sprintf("%s: do not fly on %s", d, d), character(1))
          unsched_msgs <- c(unsched_msgs, sprintf("Route %d cannot be scheduled because %s.", urn, paste(by_day_msgs, collapse=" | ")))
          next
        }
        
        # Apply UI Date filters by slot
        cand1 <- cand0 %>% dplyr::mutate(dep_date_chr = as.character(dep_date), slot_index = match(Day, days))
        if (isTRUE(input$restrict_dates_master)) {
          slot_labels <- c(input$day1, input$day2, input$day3, input$day4)
          slot_idx    <- which(slot_labels %in% DAY_LEVELS)
          
          cand1$keep_date <- TRUE
          for (duniq in unique(cand1$Day)) {
            pos <- which(days == duniq)[1]
            slot_no <- if (!is.na(pos) && length(slot_idx) >= pos) slot_idx[pos] else NA_integer_
            allowed <- if (!is.na(slot_no)) (input[[paste0("dates_slot", slot_no)]] %||% character(0)) else character(0)
            if (length(allowed)) {
              cand1$keep_date[cand1$Day == duniq] <- cand1$dep_date_chr[cand1$Day == duniq] %in% allowed
            }
          }
          
          cand1 <- cand1 %>% dplyr::filter(keep_date)
          if (!nrow(cand1)) {
            reasons <- c(reasons, "all candidate dates were filtered out by your Date filters")
            by_day_msgs <- vapply(days, function(d) sprintf("%s:...dates were filtered out by your Date filters", d), character(1))
            unsched_msgs <- c(unsched_msgs, sprintf("Route %d ca...cheduled because %s.", urn, paste(by_day_msgs, collapse=" | ")))
            next
          }
        }
        debug_note(
          day  = "ALL",
          slot = NA_integer_,
          step = "unsched_cand1",
          info = list(
            URN     = as.integer(urn),
            n_cand1 = nrow(cand1)
          )
        )
        # Compute DepMin2
        cand1$DepMin2 <- if ("DepMin" %in% names(cand1)) suppressWarnings(as.integer(cand1$DepMin)) else NA_integer_
        bad <- is.na(cand1$DepMin2) | !is.finite(cand1$DepMin2)
        if (any(bad) && "Departure Time" %in% names(cand1)) {
          cand1$DepMin2[bad] <- vapply(cand1$`Departure Time`[bad], parse_user_time, integer(1))
        }
        cand1$DepMin2 <- ((cand1$DepMin2 %% 1440) + 1440) %% 1440
        
        # IMPORTANT: Restrict diagnostics to the same effective date(s) used by the scheduler
        # (anchor date when date restriction is off; restricted dates when it is on).
        date_col <- if ("dep_date" %in% names(cand1)) "dep_date" else if ("Date" %in% names(cand1)) "Date" else NA_character_
        if (!is.na(date_col) && "Day" %in% names(cand1) && exists("effective_dates_for")) {
          cand1[[date_col]] <- as.Date(cand1[[date_col]])
          keep <- rep(TRUE, nrow(cand1))
          for (dd in unique(as.character(cand1$Day))) {
            eff <- tryCatch(effective_dates_for(dd), error = function(e) NULL)
            if (!is.null(eff) && length(eff)) {
              eff <- as.Date(eff)
              idx <- which(as.character(cand1$Day) == dd)
              keep[idx] <- cand1[[date_col]][idx] %in% eff
            }
          }
          cand1 <- cand1[keep, , drop = FALSE]
        }
        
        # Enforce latest-time cap if hard
        if (hard_latest_applies && is.finite(latest_cap_min)) {
          cand2 <- cand1 %>% dplyr::filter(DepMin2 <= latest_cap_min)
          if (!nrow(cand2)) {
            reasons <- c(reasons, sprintf("all flights depart after the latest time cap (%s)", mins_to_ampm(latest_cap_min)))
            by_day_msgs <- vapply(days, function(d) sprintf("%s: all flights depart after the latest time cap (%s)", d, mins_to_ampm(latest_cap_min)), character(1))
            unsched_msgs <- c(unsched_msgs, sprintf("Route %d cannot be scheduled because %s.", urn, paste(by_day_msgs, collapse=" | ")))
            next
          }
        } else {
          cand2 <- cand1
        }
        debug_note(
          day  = "ALL",
          slot = NA_integer_,
          step = "unsched_cand2",
          info = list(
            URN     = as.integer(urn),
            n_cand2 = nrow(cand2)
          )
        )
        skip_diag <- FALSE
        
        # Month 3: bin caps full for all bins this route can use?
        if (month == 3 && !is.null(bin_caps_now)) {
          label_bin <- function(day_chr, dep_min) {
            is_we1 <- isTRUE(day_chr %in% WEEKEND_DAYS)
            is_am1 <- isTRUE(all(is.finite(dep_min)) && all(dep_min < 12*60))
            if (!is_we1 && is_am1) "wd_am" else if (!is_we1 && !is_am1) "wd_pm" else if (is_we1 && is_am1) "we_am" else "we_pm"
          }
          cand2$bin <- mapply(label_bin, cand2$Day, cand2$DepMin2)
          bins_for <- sort(unique(as.character(cand2$bin)))
          if (length(bins_for)) {
            all_full <- all(vapply(bins_for, function(b) (bin_room_left(b) <= 0L), logical(1)))
            if (all_full) {
              # If multiple possible bins, list all for clarity
              reasons <- c(reasons, sprintf("it would exceed the maximum desired %s assigned surveys", paste(vapply(bins_for, nice_bin, character(1)), collapse = " or ")))
            }
          }
          # -- If not "all_full", see whether any under-cap placements exist ONLY on dates unusable in Date-Fit --
          skip_diag <- FALSE
          if (!isTRUE(all_full)) {
            # Map: which bins still have room?
            ok_bin <- function(b) isTRUE(bin_room_left(b) > 0L)
            ok_bins <- bins_for[vapply(bins_for, ok_bin, logical(1))]
            
            if (length(ok_bins)) {
              # Limit to candidates in bins with room
              cand_ok <- cand2 %>% dplyr::filter(bin %in% ok_bins)
              if (nrow(cand_ok)) {
                # For Date-Fit intersection, compare using the same "M-D" labels used in the fit table
                cand_ok$md <- vapply(cand_ok$dep_date, fmt_md, character(1))
                
                # Pull usable-date strings from the latest Date-Fit table
                fit <- state$date_fit
                # Find a day where none of the under-cap candidate dates are usable in the created schedule
                special_msg <- character(0)
                by_day <- split(cand_ok, cand_ok$Day)
                for (dn in names(by_day)) {
                  usable_md_dn <- character(0)
                  if (is.data.frame(fit) && nrow(fit)) {
                    row_dn <- try(fit[fit$Day == dn, "Usable Dates", drop = TRUE], silent = TRUE)
                    if (!inherits(row_dn, "try-error") && length(row_dn)) {
                      usable_md_dn <- trimws(unlist(strsplit(as.character(row_dn[1]), ",")))
                    }
                  }
                  in_use <- by_day[[dn]]$md %in% usable_md_dn
                  if (!any(in_use) && any(!in_use)) {
                    # Pick the earliest such date and format as M/D for the message
                    ix <- which.min(by_day[[dn]]$dep_date)
                    md_hyphen <- by_day[[dn]]$md[ix]
                    md_slash  <- gsub("-", "/", md_hyphen, fixed = TRUE)
                    special_msg <- sprintf(
                      "the only placement that remains under the bin caps is, %s, which is unusable in the created schedule on %s",
                      md_slash, dn
                    )
                    break
                  }
                }
                if (length(special_msg)) {
                  reasons  <- c(reasons, special_msg)
                  skip_diag <- TRUE   # Don’t add per-slot diagnostics; we already have the precise cause
                }
              }
            }
          }
        }
        
        # Per-slot full caps? (Use slot indices to disambiguate duplicates)
        # Compute slot indices then *sanitize* them so later indexing cannot error.
        # Normalize cand2$Day to a 3-letter weekday token before matching to selected slots.
        # Handles values like "Sun (1)", "Sunday", or numeric codes "1".."7".
        day_tok <- trimws(as.character(cand2$Day))
        day_num <- suppressWarnings(as.integer(day_tok))
        day_tok3 <- ifelse(
          is.finite(day_num) & day_num >= 1L & day_num <= 7L,
          c("Sun","Mon","Tue","Wed","Thu","Fri","Sat")[day_num],
          substr(day_tok, 1L, 3L)
        )
        day_tok3 <- tools::toTitleCase(tolower(day_tok3))
        day_tok3[!day_tok3 %in% c("Sun","Mon","Tue","Wed","Thu","Fri","Sat")] <- NA_character_
        cand2$slot_index <- match(day_tok3, as.character(days))
        # convert to integers and only keep valid indices (finite, >=1, <= length(days))
        elig_slots_raw <- unique(as.integer(cand2$slot_index))
        elig_slots <- elig_slots_raw[is.finite(elig_slots_raw) & elig_slots_raw >= 1L & elig_slots_raw <= length(days)]
        elig_slots <- sort(elig_slots)
        
        if (!isTRUE(skip_diag) && length(elig_slots)) {
          # now it's safe to index per_slot_full/per_slot_caps etc.
          is_full <- per_slot_full[elig_slots]
          is_full[is.na(is_full)] <- FALSE
          
          full_slots <- elig_slots[is_full]
          open_slots <- elig_slots[!is_full]
          
          # Only report "already at maximum" when *all* eligible slots are full.
          if (!isTRUE(skip_diag) && length(elig_slots)) {
            if (length(open_slots) == 0L && length(full_slots)) {
              lbls <- paste(vapply(full_slots, slot_label, character(1)), collapse = ", ")
              caps_str <- paste(vapply(full_slots, function(i) as.integer(per_slot_caps[i]), integer(1)), collapse = "/")
              if (length(unique(per_slot_caps[full_slots])) == 1) {
                reasons <- c(
                  reasons,
                  sprintf("%s %s already at its maximum of %d assigned surveys",
                          if (length(full_slots) > 1) "day slots" else "day slot",
                          lbls, as.integer(per_slot_caps[full_slots][1]))
                )
              } else {
                reasons <- c(
                  reasons,
                  sprintf("%s %s are already at their maximums (%s assigned surveys)",
                          if (length(full_slots) > 1) "day slots" else "day slot",
                          lbls, caps_str)
                )
              }
            }
          }
          
          # For subsequent hard-hours diagnostics, ignore slots that are already full
          elig_slots <- open_slots
          
        }
        
        # Rolling daily-hours window per eligible slot
        # Months 1–2 always enforce a rolling span cap; Month 3 only enforces this when Hard Hours is ON.
        if (length(elig_slots)) {
          month_idx_dbg2 <- suppressWarnings(as.integer(input$month_index))
          if (!is.finite(month_idx_dbg2) || is.na(month_idx_dbg2) || month_idx_dbg2 <= 0L) month_idx_dbg2 <- 1L
          hh_reasons <- character(0)
          
          for (i in elig_slots) {
            if (!is.finite(i) || i < 1L || i > length(days)) next
            
            enforce_hours_i <- isTRUE(month_idx_dbg2 %in% c(1L, 2L) || hard_hours_flags[i])
            if (!enforce_hours_i) next
            
            slot_rows <- cand2 %>% dplyr::filter(slot_index == i)
            if (!nrow(slot_rows)) next
            
            df_slot <- assignments[[i]]
            if (!is.data.frame(df_slot) || !nrow(df_slot)) next
            
            hours_cap_min <- as.integer(
              if (isTRUE(input$fine_tune_days)) {
                v <- nzint(input[[paste0('ft_hours_', i)]])
                if (!is.finite(v) || v <= 0L) 24L else v
              } else {
                nzint(input$max_hours) %||% 6L
              }
            )
            span_cap <- as.integer(hours_cap_min) * 60L
            
            dep_col_sched <- if ("DepMin2" %in% names(df_slot)) "DepMin2" else if ("DepMin" %in% names(df_slot)) "DepMin" else NA_character_
            slot_sched_depmins <- if (!is.na(dep_col_sched)) as.integer(df_slot[[dep_col_sched]]) else integer(0)
            if (!length(slot_sched_depmins)) next
            
            earliest_sched <- suppressWarnings(min(slot_sched_depmins, na.rm = TRUE))
            latest_sched   <- suppressWarnings(max(slot_sched_depmins, na.rm = TRUE))
            
            ws <- as.integer(latest_sched) - as.integer(span_cap)
            we <- as.integer(earliest_sched) + as.integer(span_cap)
            
            # Incorporate hard earliest/latest caps (if enabled)
            if (isTRUE(input$hard_earliest) && is.finite(earliest_cap) && is.finite(ws)) {
              ws <- as.integer(max(ws, as.integer(earliest_cap)))
            }
            if (isTRUE(input$hard_latest) && is.finite(latest_cap) && is.finite(we)) {
              we <- as.integer(min(we, as.integer(latest_cap)))
            }
            
            dep_col_cand <- if ("DepMin2" %in% names(slot_rows)) "DepMin2" else if ("DepMin" %in% names(slot_rows)) "DepMin" else NA_character_
            slot_cand_depmins <- if (!is.na(dep_col_cand)) as.integer(slot_rows[[dep_col_cand]]) else integer(0)
            if (!length(slot_cand_depmins) || !is.finite(ws) || !is.finite(we)) next
            
            inside <- slot_cand_depmins >= ws & slot_cand_depmins <= we
            if (!any(inside, na.rm = TRUE)) {
              ot <- unique(vapply(slot_cand_depmins, mins_to_ampm, character(1)))
              if (length(ot) > 1L) {
                ord <- order(vapply(ot, parse_user_time, integer(1)), na.last = TRUE)
                ot <- ot[ord]
              }
              times_csv <- if (exists("join_oxford")) join_oxford(ot) else paste(ot, collapse = ", ")
              noun <- if (length(ot) == 1L) "candidate" else "candidates"
              verb <- if (length(ot) == 1L) "is" else "are"
              
              hh_reasons <- c(
                hh_reasons,
                sprintf(
                  "outside the rolling window [%s–%s]; %s %s %s on %s",
                  mins_to_ampm(ws), mins_to_ampm(we), noun, times_csv, verb, days[i]
                )
              )
            }
          }
          
          if (length(hh_reasons)) {
            reasons <- c(reasons, unique(hh_reasons))
          }
          
          # If some selected days have no flights for this URN, add a reason noting no service on those days
          missing_days <- setdiff(days, sort(unique(as.character(cand2$Day))))
          if (length(missing_days)) {
            reasons <- c(reasons, sprintf("do not fly on %s", paste(missing_days, collapse = ", ")))
          }
        }
        
        if (!length(reasons)) {
          # Diagnose the concrete blocking constraint(s) per eligible slot for this route
          per_f_cap_diag <- as.integer(nzint(input$per_flight_cap %||% 10L))
          
          label_bin <- function(day_chr, dep_min) {
            is_we1 <- isTRUE(day_chr %in% WEEKEND_DAYS)
            is_am1 <- isTRUE(all(is.finite(dep_min)) && all(dep_min < 12*60))
            if (!is_we1 && is_am1) "wd_am" else if (!is_we1 && !is_am1) "wd_pm" else if (is_we1 && is_am1) "we_am" else "we_pm"
          }
          
          # Prepare candidate rows after all upstream filters we already applied (cand2)
          cand_diag <- cand2 %>% dplyr::mutate(slot_index = match(Day, days))
          if (!nrow(cand_diag)) {
            reasons <- c(reasons, "all candidate dates/times were filtered by earlier constraints (date filters or latest-time cap)")
          } else {
            # Inspect each eligible slot separately
            diag_msgs <- character(0)
            for (i in sort(unique(as.integer(cand_diag$slot_index)))) {
              if (is.na(i)) next
              dname <- days[i]
              slot_rows <- cand_diag %>% dplyr::filter(slot_index == i)
              if (!nrow(slot_rows)) next
              
              # Current slot schedule & usage
              df_slot <- if (i >= 1L && i <= length(assignments)) assignments[[i]] else NULL
              slot_used <- if (is.data.frame(df_slot) && nrow(df_slot)) sum(df_slot$`Assigned Surveys`, na.rm = TRUE) else 0L
              slot_cap  <- as.integer((per_slot_caps[i]) %||% 40L)
              slot_full_flag <- slot_used >= slot_cap
              
              # Hard-hours limit for this slot (span must stay within cap if hard_hours_flags[i] is TRUE)
              hard_hours_on <- isTRUE(hard_hours_flags[i])
              hours_cap_min <- {
                if (isTRUE(input$fine_tune_days)) {
                  v <- nzint(input[[paste0("ft_hours_", i)]])
                  if (!is.finite(v) || v <= 0L) 24L else v
                } else {
                  v <- nzint(input$max_hours)
                  if (!is.finite(v) || v <= 0L) 6L else v
                }
              }
              span_cap <- as.integer(pmax(1L, hours_cap_min) * 60L)
              slot_depmins <- if (is.data.frame(df_slot) && nrow(df_slot)) as.integer(df_slot$DepMin) else integer(0)
              
              # Analyze each candidate departure time for this slot
              # Collect candidate times that fall outside the slot's hard-hours window for one grouped message later
              outside_times <- character(0)
              for (r in seq_len(nrow(slot_rows))) {
                depm <- as.integer(slot_rows$DepMin2[r])
                bin_name <- if (month == 3) label_bin(dname, depm) else NA_character_
                # 1) Per-day cap
                if (slot_full_flag) {
                  diag_msgs <- c(diag_msgs, sprintf("blocked on %s by per-day cap (used %d / cap %d)", dname, slot_used, slot_cap))
                  next
                }
                # 2) Month-3 bin cap (hard)
                if (month == 3 && !is.null(bin_caps_now)) {
                  room_left <- bin_room_left(bin_name)
                  if (isTRUE(!is.infinite(room_left) && (room_left <= 0L))) {
                    pretty_bin <- switch(bin_name, "wd_am"="Weekday AM", "wd_pm"="Weekday PM", "we_am"="Weekend AM", "we_pm"="Weekend PM", "(bin)")
                    diag_msgs <- c(diag_msgs, sprintf("blocked on %s by Month-3 bin cap: %s has no room left", dname, pretty_bin))
                    next
                  }
                }
                # 3) Daily-hours span / rolling window
                # Months 1–2: always enforce a rolling span cap (earliest→latest must stay ≤ cap).
                # Month 3: only enforce when Hard Hours is ON for this slot.
                month_idx <- as.integer(input$month_index %||% 1L)
                enforce_hours_here <- isTRUE(month_idx %in% c(1L, 2L) || hard_hours_on)
                if (enforce_hours_here) {
                  if (month_idx %in% c(1L, 2L)) {
                    # Rolling window: expand with each pick; enforce only span ≤ cap
                    mins_all <- sort(unique(as.integer(c(slot_depmins, depm))))
                    s <- suppressWarnings(min(mins_all))
                    e <- suppressWarnings(max(mins_all))
                    if (isTRUE(is.finite(s) && is.finite(e) && ((e - s) > span_cap))) {
                      outside_times <- c(outside_times, mins_to_ampm(depm))
                      next
                    }
                  } else {
                    # Month 3: enforce pre-planned slot window when defined
                    w <- if (i >= 1L && i <= length(slot_win)) slot_win[[i]] else NULL
                    if (!is.null(w) && all(is.finite(w$start)) && all(is.finite(w$end)) && month == 3L) {
                      # Month 3: enforce hard window bounds in diagnostics
                      if (depm < as.integer(w$start) || depm > as.integer(w$end)) {
                        outside_times <- c(outside_times, mins_to_ampm(depm))
                        next
                      }
                      mins_all <- sort(unique(as.integer(c(slot_depmins, depm))))
                      s <- max(as.integer(w$start), suppressWarnings(min(mins_all)))
                      e <- min(as.integer(w$end),   suppressWarnings(max(mins_all)))
                      if (isTRUE(is.finite(s) && is.finite(e) && ((e - s) > span_cap))) {
                        outside_times <- c(outside_times, mins_to_ampm(depm))
                        next
                      }
                    } else {
                      # Months 1–2 (or no window): only enforce the rolling-span cap
                      mins_all <- sort(unique(as.integer(c(slot_depmins, depm))))
                      s <- suppressWarnings(min(mins_all))
                      e <- suppressWarnings(max(mins_all))
                      if (isTRUE(is.finite(s) && is.finite(e) && ((e - s) > span_cap))) {
                        outside_times <- c(outside_times, mins_to_ampm(depm))
                        next
                      }
                    }
                  }
                }
                # 4) Per-flight cap (10) at THIS departure time within this slot
                same_dep_assigned <- 0L
                if (is.data.frame(df_slot) && nrow(df_slot)) {
                  same_dep_assigned <- df_slot %>%
                    dplyr::filter(`Unique Route Number` == urn, DepMin == depm) %>%
                    dplyr::summarise(S = sum(`Assigned Surveys`, na.rm = TRUE), .groups = "drop") %>%
                    dplyr::pull(S) %>% { if (length(.)==0) 0L else as.integer(.) }
                }
                if (isTRUE((same_dep_assigned %||% 0L) >= per_f_cap_diag)) {
                  diag_msgs <- c(
                    diag_msgs,
                    sprintf(
                      "blocked on %s by per-flight cap at this departure time (already scheduled %d/%d at %s)",
                      dname, same_dep_assigned, per_f_cap_diag, mins_to_ampm(depm)
                    )
                  )
                  next
                }
                # 4b) Interflight spacing against existing schedule in this slot
                blocked_spacing <- character(0)
                if (((as.integer(input$month_index) %||% 1L) %in% c(1L, 2L) || isTRUE(input$enforce_spacing)) && is.data.frame(df_slot) && nrow(df_slot)) {
                  # Candidate concourse for this route/time
                  cand_cc <- cclean(slot_rows$Concourse[r])
                  
                  # Previous neighbor (scheduled before this candidate)
                  prev_dep <- suppressWarnings(max(df_slot$DepMin[df_slot$DepMin < depm], na.rm = TRUE))
                  if (is.finite(prev_dep)) {
                    prev_rows <- df_slot[df_slot$DepMin == prev_dep, , drop = FALSE]
                    prev_S    <- as.integer(sum(prev_rows$`Assigned Surveys`, na.rm = TRUE))
                    prev_cc   <- cclean(prev_rows$Concourse[1])
                    need_prev <- as.integer(spacing_after(prev_S, concourse_change = !identical(prev_cc, cand_cc)))
                    gap_prev  <- as.integer(depm - prev_dep)
                    if (gap_prev < need_prev) {
                      blocked_spacing <- c(
                        blocked_spacing,
                        sprintf("%s needs ≥ %d min after %s, only %d",
                                mins_to_ampm(depm), need_prev, mins_to_ampm(prev_dep), gap_prev)
                      )
                    }
                  }
                  
                  # Next neighbor (scheduled after this candidate)
                  next_dep <- suppressWarnings(min(df_slot$DepMin[df_slot$DepMin > depm], na.rm = TRUE))
                  if (is.finite(next_dep)) {
                    next_rows <- df_slot[df_slot$DepMin == next_dep, , drop = FALSE]
                    next_cc   <- cclean(next_rows$Concourse[1])
                    # Even 1 survey requires >=10 min (+15 if concourse changes)
                    need_next <- as.integer(spacing_after(1L, concourse_change = !identical(cand_cc, next_cc)))
                    gap_next  <- as.integer(next_dep - depm)
                    if (gap_next < need_next) {
                      blocked_spacing <- c(
                        blocked_spacing,
                        sprintf("%s needs ≥ %d min before %s, only %d",
                                mins_to_ampm(depm), need_next, mins_to_ampm(next_dep), gap_next)
                      )
                    }
                  }
                }
                
                if (length(blocked_spacing)) {
                  msg_sp <- sprintf("would violate interflight spacing on %s", dname)
                  if (!any(grepl(sprintf("would violate interflight spacing on %s\\b", dname), diag_msgs))) {
                    diag_msgs <- c(diag_msgs, msg_sp)
                  }
                  next
                }
              }
            }
            
            # If any candidates fell outside the rolling window, add a single grouped message
            if (length(outside_times)) {
              month_idx2 <- as.integer(input$month_index %||% 1L)
              
              # True rolling bounds based on what is already scheduled on this day:
              #   [latest_scheduled - cap, earliest_scheduled + cap]
              slot_sched_depmins <- if (is.data.frame(df_slot) && nrow(df_slot)) as.integer(df_slot$DepMin) else integer(0)
              w <- if (i >= 1L && i <= length(slot_win)) slot_win[[i]] else NULL
              
              ws <- NA_integer_
              we <- NA_integer_
              if (length(slot_sched_depmins)) {
                earliest_sched <- suppressWarnings(min(slot_sched_depmins, na.rm = TRUE))
                latest_sched   <- suppressWarnings(max(slot_sched_depmins, na.rm = TRUE))
                ws <- as.integer(latest_sched) - as.integer(span_cap)
                we <- as.integer(earliest_sched) + as.integer(span_cap)
              } else if (month_idx2 == 3L && !is.null(w) && is.finite(w$start) && is.finite(w$end)) {
                # Month 3 fallback (rare): use pre-planned slot window if that's what was enforced
                ws <- as.integer(w$start)
                we <- as.integer(w$end)
              }
              
              # Incorporate hard earliest/latest caps (if enabled)
              if (isTRUE(input$hard_earliest) && is.finite(earliest_cap) && is.finite(ws)) {
                ws <- as.integer(max(ws, as.integer(earliest_cap)))
              }
              if (isTRUE(input$hard_latest) && is.finite(latest_cap) && is.finite(we)) {
                we <- as.integer(min(we, as.integer(latest_cap)))
              }
              
              if (is.finite(ws) && is.finite(we) && ws <= we) {
                # De-duplicate times & sort chronologically (earliest → latest)
                ot <- unique(outside_times)
                if (length(ot) > 1L) {
                  ord <- order(vapply(ot, parse_user_time, integer(1)), na.last = TRUE)
                  ot <- ot[ord]
                }
                
                # Oxford join (use local helper if present)
                times_csv <- if (exists("join_oxford")) join_oxford(ot) else paste(ot, collapse = ", ")
                
                noun <- if (length(ot) == 1L) "candidate" else "candidates"
                verb <- if (length(ot) == 1L) "is" else "are"
                
                diag_msgs <- c(diag_msgs, sprintf(
                  "outside the rolling window [%s–%s]; %s %s %s on %s",
                  mins_to_ampm(ws), mins_to_ampm(we), noun, times_csv, verb, dname
                ))
              }
            }
            
            if (length(diag_msgs)) {
              # If a Month-3 bin cap blocked any slot, suppress the generic optimization-order message
              has_bin_cap <- any(grepl("Month-3 bin cap", diag_msgs, fixed = TRUE))
              if (isTRUE(has_bin_cap)) {
                diag_msgs <- diag_msgs[!grepl("global optimization order/remaining", diag_msgs, fixed = TRUE)]
              }
              # Debug: capture per-URN, per-slot diagnostic summary
              cand_times <- tryCatch(
                {
                  if ("DepMin2" %in% names(slot_rows)) {
                    paste(
                      sort(unique(vapply(slot_rows$DepMin2, mins_to_ampm, character(1)))),
                      collapse = ", "
                    )
                  } else if ("DepMin" %in% names(slot_rows)) {
                    paste(
                      sort(unique(vapply(slot_rows$DepMin, mins_to_ampm, character(1)))),
                      collapse = ", "
                    )
                  } else {
                    ""
                  }
                },
                error = function(e) ""
              )
              debug_note(
                day  = dname,
                slot = i,
                step = "unsched_diag_slot",
                info = list(
                  URN          = as.integer(urn),
                  CandTimes    = cand_times,
                  BlockReasons = paste(unique(diag_msgs), collapse = " | ")
                )
              )
              reasons <- c(reasons, unique(diag_msgs))
            } else {
              reasons <- c(reasons, "no eligible placement under hard constraints (per-day cap, Month-3 bin caps, hard-hours span, or per-flight 10 cap)")
            }
          }
        }
        # Build per-day messages so every selected day shows a reason
        # Ensure per-flight cap exists for downstream per-day diagnostics (even when the deep-diagnostic branch isn't hit)
        per_f_cap_diag <- as.integer(nzint(input$per_flight_cap %||% 10L))
        by_day_msgs <- vapply(days, function(d) {
          # reasons that explicitly mention this day
          msgs_d <- reasons[grepl(paste0("\\b", d, "\\b"), reasons, perl = TRUE)]
          # days with no flights at all for this URN among selected days
          missing_days <- setdiff(days, unique(cand0$Day))
          if (!length(msgs_d) && (d %in% missing_days)) {
            msgs_d <- sprintf("do not fly on %s", d)
          }
          # If the route does fly on this weekday, but all flights were filtered out by the
          # effective date(s) chosen for that weekday (anchor/restricted dates), say that
          if (!length(msgs_d)) {
            uc2 <- if ("URN" %in% names(cand2)) "URN" else if ("Unique Route Number" %in% names(cand2)) "Unique Route Number" else NA_character_
            if (!is.na(uc2) && "Day" %in% names(cand2)) {
              any_for_day_after_date_filter <- any(cand2$Day == d & as.integer(cand2[[uc2]]) == as.integer(urn))
              any_for_day_before_date_filter <- any(cand0$Day == d)
              if (!any_for_day_after_date_filter && any_for_day_before_date_filter) {
                msgs_d <- sprintf("no flights on the selected date(s) on %s", d)
              }
            }
          }
          # if nothing day-specific was captured, include any global (day-agnostic) reasons
          if (!length(msgs_d)) {
            globals <- reasons[!grepl("\\b(Sun|Mon|Tue|Wed|Thu|Fri|Sat)\\b", reasons)]
            if (length(globals)) msgs_d <- unique(globals)
          }
          # final fallback (rare): before defaulting to "tie-breakers", derive a concrete per-day cause
          if (!length(msgs_d)) {
            i_d <- match(d, days)
            
            # Determine if the day-slot is already full
            df_slot <- NULL
            used_now <- 0L
            slot_cap <- as.integer(per_slot_caps[i_d] %||% 0L)
            if (is.finite(i_d) && i_d >= 1L && i_d <= length(assignments)) {
              df_slot <- assignments[[i_d]]
              if (is.data.frame(df_slot) && nrow(df_slot)) {
                used_now <- as.integer(sum(df_slot$`Assigned Surveys`, na.rm = TRUE))
              }
            }
            slot_full <- is.finite(slot_cap) && slot_cap > 0L && used_now >= slot_cap
            
            if (!isTRUE(slot_full)) {
              msgs_try <- character(0)
              
              # Candidate rows for *this route on this day* after upstream filters
              urn_col_cand2 <- if ("URN" %in% names(cand2)) {
                "URN"
              } else if ("Unique Route Number" %in% names(cand2)) {
                "Unique Route Number"
              } else {
                NA_character_
              }
              
              if (!is.na(urn_col_cand2) && "Day" %in% names(cand2)) {
                cand_day <- cand2[
                  cand2$Day == d & as.integer(cand2[[urn_col_cand2]]) == as.integer(urn),
                  ,
                  drop = FALSE
                ]
              } else {
                cand_day <- cand2[0, , drop = FALSE]
              }
              # Date-fit diagnostic: restrict candidates to the selected schedule date for this slot (if available).
              slot_dt <- as.Date(NA)
              if (exists("slot_dates")) {
                if (is.list(slot_dates) && length(slot_dates) >= i_d) {
                  slot_dt <- as.Date(slot_dates[[i_d]])
                } else if (!is.list(slot_dates) && length(slot_dates) >= i_d) {
                  slot_dt <- as.Date(slot_dates[i_d])
                }
              }
              
              date_col_cand <- if ("dep_date" %in% names(cand_day)) "dep_date" else if ("Date" %in% names(cand_day)) "Date" else NA_character_
              if (!is.na(date_col_cand) && is.finite(i_d) && nrow(cand_day) && is.finite(suppressWarnings(as.numeric(slot_dt)))) {
                cand_day <- cand_day[as.Date(cand_day[[date_col_cand]]) == slot_dt, , drop = FALSE]
                if (!nrow(cand_day)) {
                  msgs_try <- c(msgs_try, sprintf("it does not fly on the selected date (%s)", format(slot_dt, "%m-%d")))
                }
              }
              
              # A) Rolling daily-hours window check for this day
              # Months 1–2 always enforce a rolling span cap; Month 3 only enforces this when Hard Hours is ON.
              month_idx_dbg <- suppressWarnings(as.integer(input$month_index))
              if (!is.finite(month_idx_dbg) || is.na(month_idx_dbg) || month_idx_dbg <= 0L) month_idx_dbg <- 1L
              enforce_hours_dbg <- isTRUE((month_idx_dbg %in% c(1L, 2L)) || isTRUE(hard_hours_flags[i_d]))
              if (enforce_hours_dbg) {
                hours_cap_min <- as.integer(
                  if (isTRUE(input$fine_tune_days)) {
                    v <- nzint(input[[paste0('ft_hours_', i_d)]])
                    if (!is.finite(v) || v <= 0L) 24L else v
                  } else {
                    nzint(input$max_hours) %||% 6L
                  }
                )
                span_cap <- as.integer(hours_cap_min) * 60L
                
                # Robust dep-minute extraction for candidates + already scheduled flights
                dep_col_cand <- if ("DepMin2" %in% names(cand_day)) {
                  "DepMin2"
                } else if ("DepMin" %in% names(cand_day)) {
                  "DepMin"
                } else if ("Departure Time" %in% names(cand_day)) {
                  "Departure Time"
                } else {
                  NA_character_
                }
                
                slot_cand_depmins <- if (nrow(cand_day) && !is.na(dep_col_cand)) {
                  if (dep_col_cand == "Departure Time") {
                    vapply(cand_day[[dep_col_cand]], parse_user_time, integer(1))
                  } else {
                    as.integer(cand_day[[dep_col_cand]])
                  }
                } else integer(0)
                
                dep_col_sched <- if (is.data.frame(df_slot) && nrow(df_slot)) {
                  if ("DepMin2" %in% names(df_slot)) {
                    "DepMin2"
                  } else if ("DepMin" %in% names(df_slot)) {
                    "DepMin"
                  } else if ("Departure Time" %in% names(df_slot)) {
                    "Departure Time"
                  } else {
                    NA_character_
                  }
                } else {
                  NA_character_
                }
                
                slot_sched_depmins <- if (is.data.frame(df_slot) && nrow(df_slot) && !is.na(dep_col_sched)) {
                  if (dep_col_sched == "Departure Time") {
                    vapply(df_slot[[dep_col_sched]], parse_user_time, integer(1))
                  } else {
                    as.integer(df_slot[[dep_col_sched]])
                  }
                } else integer(0)
                ws <- NA_integer_
                we <- NA_integer_
                
                # Preferred: true rolling window bounds based on what is already scheduled on this day
                if (length(slot_sched_depmins)) {
                  earliest_sched <- suppressWarnings(min(slot_sched_depmins, na.rm = TRUE))
                  latest_sched   <- suppressWarnings(max(slot_sched_depmins, na.rm = TRUE))
                  ws <- as.integer(latest_sched) - as.integer(span_cap)
                  we <- as.integer(earliest_sched) + as.integer(span_cap)
                } else if (month_idx_dbg == 3L) {
                  # Month 3 fallback (rare): if a pre-planned slot window exists, use it
                  w <- if (i_d >= 1L && i_d <= length(slot_win)) slot_win[[i_d]] else NULL
                  if (!is.null(w) && is.finite(w$start) && is.finite(w$end)) {
                    ws <- as.integer(w$start)
                    we <- as.integer(w$end)
                  }
                }
                
                # Incorporate hard earliest/latest caps (if enabled)
                if (isTRUE(input$hard_earliest) && is.finite(earliest_cap) && is.finite(ws)) {
                  ws <- as.integer(max(ws, as.integer(earliest_cap)))
                }
                if (isTRUE(input$hard_latest) && is.finite(latest_cap) && is.finite(we)) {
                  we <- as.integer(min(we, as.integer(latest_cap)))
                }
                
                if (is.finite(ws) && is.finite(we) && length(slot_cand_depmins)) {
                  
                  # Earliest/latest time-cap diagnostics (independent of the rolling window)
                  if (isTRUE(input$hard_earliest) && is.finite(earliest_cap)) {
                    bad <- slot_cand_depmins[is.finite(slot_cand_depmins) & slot_cand_depmins < earliest_cap]
                    if (length(bad)) {
                      ot <- unique(vapply(bad, mins_to_ampm, character(1)))
                      if (length(ot) > 1L) {
                        ord <- order(vapply(ot, parse_user_time, integer(1)), na.last = TRUE)
                        ot <- ot[ord]
                      }
                      times_csv <- if (exists("join_oxford")) join_oxford(ot) else paste(ot, collapse = ", ")
                      verb <- if (length(ot) == 1L) "is" else "are"
                      msgs_try <- c(
                        msgs_try,
                        sprintf(
                          "departs before the earliest time cap (%s); candidate %s %s on %s",
                          mins_to_ampm(as.integer(earliest_cap)),
                          if (nzchar(times_csv)) times_csv else "time",
                          if (nzchar(verb)) verb else "is",
                          d
                        )
                      )
                    }
                  }
                  
                  if (isTRUE(input$hard_latest) && is.finite(latest_cap)) {
                    bad <- slot_cand_depmins[is.finite(slot_cand_depmins) & slot_cand_depmins > latest_cap]
                    if (length(bad)) {
                      ot <- unique(vapply(bad, mins_to_ampm, character(1)))
                      if (length(ot) > 1L) {
                        ord <- order(vapply(ot, parse_user_time, integer(1)), na.last = TRUE)
                        ot <- ot[ord]
                      }
                      times_csv <- if (exists("join_oxford")) join_oxford(ot) else paste(ot, collapse = ", ")
                      verb <- if (length(ot) == 1L) "is" else "are"
                      msgs_try <- c(
                        msgs_try,
                        sprintf(
                          "departs after the latest time cap (%s); candidate %s %s on %s",
                          mins_to_ampm(as.integer(latest_cap)),
                          if (nzchar(times_csv)) times_csv else "time",
                          if (nzchar(verb)) verb else "is",
                          d
                        )
                      )
                    }
                  }
                  
                  # Rolling-window violations: list the times that are outside the rolling window
                  out <- slot_cand_depmins[is.finite(slot_cand_depmins) & (slot_cand_depmins < ws | slot_cand_depmins > we)]
                  
                  # If hard caps were already reported above, don't double-count them as "rolling window"
                  if (isTRUE(input$hard_earliest) && is.finite(earliest_cap)) out <- out[out >= earliest_cap]
                  if (isTRUE(input$hard_latest) && is.finite(latest_cap))   out <- out[out <= latest_cap]
                  
                  if (length(out)) {
                    ot <- unique(vapply(out, mins_to_ampm, character(1)))
                    if (length(ot) > 1L) {
                      ord <- order(vapply(ot, parse_user_time, integer(1)), na.last = TRUE)
                      ot <- ot[ord]
                    }
                    times_csv <- if (exists("join_oxford")) join_oxford(ot) else paste(ot, collapse = ", ")
                    noun <- if (length(ot) == 1L) "candidate" else "candidates"
                    verb <- if (length(ot) == 1L) "is" else "are"
                    
                    msgs_try <- c(
                      msgs_try,
                      sprintf(
                        "outside the rolling window [%s–%s]; %s %s %s on %s",
                        mins_to_ampm(ws), mins_to_ampm(we),
                        noun,
                        if (nzchar(times_csv)) times_csv else "time",
                        verb,
                        d
                      )
                    )
                  }
                }
              }
              
              # B) Interflight spacing against the *final* schedule for this day
              if (is.data.frame(df_slot) && nrow(df_slot) && nrow(cand_day)) {
                
                # Robust dep-minute extraction for scheduled slot + candidate rows
                dep_col_sched <- if ("DepMin2" %in% names(df_slot)) {
                  "DepMin2"
                } else if ("DepMin" %in% names(df_slot)) {
                  "DepMin"
                } else if ("Departure Time" %in% names(df_slot)) {
                  "Departure Time"
                } else {
                  NA_character_
                }
                
                dep_col_cand <- if ("DepMin2" %in% names(cand_day)) {
                  "DepMin2"
                } else if ("DepMin" %in% names(cand_day)) {
                  "DepMin"
                } else if ("Departure Time" %in% names(cand_day)) {
                  "Departure Time"
                } else {
                  NA_character_
                }
                
                dep_vec <- if (!is.na(dep_col_sched)) {
                  if (dep_col_sched == "Departure Time") {
                    vapply(df_slot[[dep_col_sched]], parse_user_time, integer(1))
                  } else {
                    as.integer(df_slot[[dep_col_sched]])
                  }
                } else integer(0)
                
                cand_depmins_int <- if (!is.na(dep_col_cand)) {
                  if (dep_col_cand == "Departure Time") {
                    vapply(cand_day[[dep_col_cand]], parse_user_time, integer(1))
                  } else {
                    as.integer(cand_day[[dep_col_cand]])
                  }
                } else integer(0)
                
                dep_vec <- as.integer(dep_vec)
                cand_depmins_int <- as.integer(cand_depmins_int)
                
                fits_any <- FALSE
                depmins <- sort(unique(cand_depmins_int[is.finite(cand_depmins_int)]))
                
                # Only test spacing for candidate times that are otherwise time-feasible (caps + rolling window)
                depmins_for_spacing <- depmins
                if (is.finite(ws) && is.finite(we)) {
                  depmins_for_spacing <- depmins_for_spacing[depmins_for_spacing >= ws & depmins_for_spacing <= we]
                }
                if (isTRUE(input$hard_earliest) && is.finite(earliest_cap)) {
                  depmins_for_spacing <- depmins_for_spacing[depmins_for_spacing >= earliest_cap]
                }
                if (isTRUE(input$hard_latest) && is.finite(latest_cap)) {
                  depmins_for_spacing <- depmins_for_spacing[depmins_for_spacing <= latest_cap]
                }
                
                # Guess how many surveys we'd put on the candidate flight for spacing purposes
                cand_need_total <- suppressWarnings(as.integer(routes_updated$`Assigned Surveys`[routes_updated$`Unique Route Number` == urn][1]))
                if (!is.finite(cand_need_total) || is.na(cand_need_total) || cand_need_total <= 0L) cand_need_total <- 1L
                cand_S_guess <- as.integer(max(1L, min(cand_need_total, per_f_cap_diag)))
                
                if (length(dep_vec) && length(depmins_for_spacing)) {
                  for (depm in depmins_for_spacing) {
                    cand_idx <- which(cand_depmins_int == depm)[1]
                    cand_cc  <- if ("Concourse" %in% names(cand_day)) cclean(cand_day$Concourse[cand_idx]) else ""
                    
                    # Previous neighbor
                    prev_dep <- suppressWarnings(max(dep_vec[dep_vec < depm], na.rm = TRUE))
                    prev_ok  <- TRUE
                    if (is.finite(prev_dep)) {
                      prev_rows <- df_slot[dep_vec == prev_dep, , drop = FALSE]
                      prev_S    <- as.integer(sum(nzint(prev_rows$`Assigned Surveys`), na.rm = TRUE))
                      prev_cc   <- cclean(prev_rows$Concourse[1])
                      need_prev <- as.integer(spacing_after(prev_S, concourse_change = !identical(prev_cc, cand_cc)))
                      gap_prev  <- as.integer(depm - prev_dep)
                      if (gap_prev < need_prev) prev_ok <- FALSE
                    }
                    
                    # Next neighbor
                    next_dep <- suppressWarnings(min(dep_vec[dep_vec > depm], na.rm = TRUE))
                    next_ok  <- TRUE
                    if (is.finite(next_dep)) {
                      next_rows <- df_slot[dep_vec == next_dep, , drop = FALSE]
                      next_cc   <- cclean(next_rows$Concourse[1])
                      need_next <- as.integer(spacing_after(cand_S_guess, concourse_change = !identical(cand_cc, next_cc)))
                      gap_next  <- as.integer(next_dep - depm)
                      if (gap_next < need_next) next_ok <- FALSE
                    }
                    
                    if (isTRUE(prev_ok) && isTRUE(next_ok)) { fits_any <- TRUE; break }
                  }
                  
                  if (!isTRUE(fits_any)) {
                    ot <- unique(vapply(depmins_for_spacing, mins_to_ampm, character(1)))
                    if (length(ot) > 1L) {
                      ord <- order(vapply(ot, parse_user_time, integer(1)), na.last = TRUE)
                      ot <- ot[ord]
                    }
                    times_csv <- if (exists("join_oxford")) join_oxford(ot) else paste(ot, collapse = ", ")
                    verb <- if (length(ot) == 1L) "is" else "are"
                    
                    msgs_try <- c(msgs_try, "would violate interflight spacing")
                  }
                }
              }
              if (length(msgs_try)) {
                msgs_d <- unique(msgs_try)
              } else {
                msgs_d <- "a reason unknown"
                if (is.finite(as.integer(state$debug_urn %||% NA_integer_)) &&
                    as.integer(state$debug_urn %||% NA_integer_) == as.integer(urn)) {
                  debug_note(
                    "ALL", NA, "unsched_fallback_score_ordering",
                    list(
                      trace_urn = as.integer(urn),
                      day       = as.character(d)
                    )
                  )
                }
              }
            } else {
              # If the slot is full, say so explicitly
              msgs_d <- sprintf("day slot %s already at its maximum of %d assigned surveys on %s",
                                d, slot_cap, d)
            }
          }
          sprintf("%s: %s", d, paste(unique(msgs_d), collapse="; "))
        }, character(1))
        unsched_msgs <- c(unsched_msgs, sprintf("Route %d cannot be scheduled because %s.", urn, paste(by_day_msgs, collapse=" | ")))
      }
      # ---- Normalize day-specific reasons by consolidating repeated messages across days ----
      if (length(unsched_msgs)) {
        condense_day_reasons <- function(msg) {
          # Extract the reason blob after "because ..."
          m <- regexec("^Route\\s+\\d+\\s+cannot be scheduled because\\s+(.*?)(?:\\.)?$", msg)
          mm <- regmatches(msg, m)[[1]]
          if (length(mm) < 2) return(msg)
          reason_blob <- trimws(mm[2])
          parts <- strsplit(reason_blob, "\\s*\\|\\s*")[[1]]
          
          # Helpers
          DAY_LEVELS <- c("Sun","Mon","Tue","Wed","Thu","Fri","Sat")
          join_days <- function(x, conj_two = "and"){
            x <- as.character(x)
            if (length(x) <= 1) return(paste(x, collapse = ""))
            if (length(x) == 2) return(paste(x, collapse = paste0(" ", conj_two, " ")))
            paste0(paste(x[-length(x)], collapse = ", "), ", and ", x[length(x)])
          }
          order_days <- function(dv) {
            dv <- unique(as.character(dv))
            dv[order(match(dv, DAY_LEVELS))]
          }
          norm_key <- function(txt){
            s <- gsub("\\.+$", "", trimws(txt))
            s <- gsub("\\s+", " ", s)
            # Remove only a *trailing* day label (do not remove mid-sentence day mentions)
            s <- gsub("\\s+(on|for)\\s+(Sun|Mon|Tue|Wed|Thu|Fri|Sat)\\b(?:\\s*\\([^)]*\\))?\\s*$", "", s)
            s <- gsub(",\\s*(Sun|Mon|Tue|Wed|Thu|Fri|Sat)\\b(?:\\s*\\([^)]*\\))?\\s*$", "", s)
            if (grepl("^do not fly( on [A-Za-z]{3})?$", s)) return("do_not_fly")
            # Treat any old “eligible under hard constraints …” text as ordering/tie-breaker
            if (grepl("^eligible( on [A-Za-z]{3})? under hard co...ded by global optimization order/remaining at other slots$", s))
              return("score_ordering")
            if (grepl("^would violate interflight spacing", s)) return("interflight_spacing")
            if (grepl("^all flights depart after the latest time cap \\(", s)) return("after_latest")
            if (grepl("^adding it would go over the max-hours constraint", s)) return("daily_hours_over")
            if (grepl("^a reason unknown$", s)) return("score_ordering")
            s
          }
          base_text <- function(key, sample_txt){
            if (key == "do_not_fly") return("it does not fly")
            if (key == "interflight_spacing") return("would violate interflight spacing")
            if (key %in% c("after_latest","daily_hours_over","score_ordering")) {
              # Strip only a *trailing* day label (keep mid-sentence day mentions)
              s <- gsub("\\s+(on|for)\\s+(Sun|Mon|Tue|Wed|Thu|Fri|Sat)\\b(?:\\s*\\([^)]*\\))?\\s*$", "", sample_txt)
              s <- gsub("\\s+", " ", trimws(s))
              return(s)
            }
            # Default: also remove only a trailing day label to avoid duplicates
            s <- gsub("\\s+(on|for)\\s+(Sun|Mon|Tue|Wed|Thu|Fri|Sat)\\b(?:\\s*\\([^)]*\\))?\\s*$", "", sample_txt)
            gsub("\\s+", " ", trimws(s))
          }
          
          # Group identical normalized reasons and collect their days
          day_map <- list()    # key -> vector of days
          sample  <- list()    # key -> sample text per key
          globals <- character(0)
          for (p in parts) {
            p <- trimws(p)
            m2 <- regexec("^([A-Za-z]{3}):\\s*(.*)$", p)
            mm2 <- regmatches(p, m2)[[1]]
            if (length(mm2) >= 3) {
              day   <- mm2[2]
              rtxt0 <- trimws(mm2[3])
              
              # Split multiple same-day reasons that were joined with ";"
              clauses_d <- unlist(strsplit(rtxt0, "\\s*;\\s*", perl = TRUE))
              clauses_d <- trimws(clauses_d)
              clauses_d <- clauses_d[nzchar(clauses_d)]
              
              if (length(clauses_d)) {
                for (rtxt in clauses_d) {
                  key <- norm_key(rtxt)
                  day_map[[key]] <- c(day_map[[key]], day)
                  if (is.null(sample[[key]])) sample[[key]] <- rtxt
                }
              }
            } else {
              globals <- c(globals, p)
            }
          }
          
          new_parts <- character(0)
          if (length(day_map)) {
            by_days <- list()
            
            for (key in names(day_map)) {
              ds <- order_days(day_map[[key]])
              if (identical(key, "do_not_fly") && length(ds) >= 3L) {
                ds_str <- paste0(paste(ds[-length(ds)], collapse = ", "), ", or ", ds[length(ds)])
              } else {
                conj_two <- if (identical(key, "do_not_fly")) "or" else "and"
                ds_str <- join_days(ds, conj_two = conj_two)
              }
              
              bt <- base_text(key, sample[[key]] %||% "")
              if (nzchar(bt)) by_days[[ds_str]] <- c(by_days[[ds_str]], bt)
            }
            
            for (ds_str in names(by_days)) {
              bt_vec <- by_days[[ds_str]]
              bt_vec <- bt_vec[nzchar(bt_vec)]
              if (!length(bt_vec)) next
              bt_join <- if (length(bt_vec) == 1L) bt_vec else paste(bt_vec, collapse = "; ")
              new_parts <- c(new_parts, sprintf("%s on %s", bt_join, ds_str))
            }
          }
          if (length(globals)) {
            gl <- unique(globals)
            
            # Drop global 'do not fly ...' fragments so we only use the normalized, day-attached version
            gl <- gl[ !grepl("^(?i)do\\s+not\\s+fly(\\s+on\\s+.*)?$", gl, perl = TRUE) ]
            
            # Drop standalone day tokens like "Thu" (optionally with a count in parens) or ", Thu"
            gl <- gl[ !grepl("^,?\\s*(Sun|Mon|Tue|Wed|Thu|Fri|Sat)\\b(?:\\s*\\([^)]*\\))?$", gl) ]
            
            # Drop anything that's only whitespace after trimming
            gl <- gl[ nzchar(trimws(gl)) ]
            
            new_parts <- c(new_parts, gl)
          }
          new_reason <- paste(unique(new_parts), collapse = " | ")
          sub("because\\s+.*$", paste0("because ", new_reason, "."), msg)
        }
        
        # Apply consolidation pass to every unscheduled message
        unsched_msgs <- vapply(unsched_msgs, condense_day_reasons, character(1))
      }
      # ---- Group identical reasons and fix singular/plural grammar ----
      route_reason <- stringr::str_match(
        unsched_msgs,
        "^Route\\s+(\\d+)\\s+cannot be scheduled because\\s+(.*?)(?:\\.)?$"
      )
      valid <- !is.na(route_reason[, 1])
      
      if (any(valid)) {
        df <- tibble::tibble(
          urn    = as.integer(route_reason[valid, 2]),
          reason = gsub("\\s+", " ", trimws(route_reason[valid, 3]))
        )
        
        # Oxford-join helper (uses your local one if present)
        join_oxford_local <- if (exists("join_oxford")) join_oxford else function(x){
          x <- as.character(x)
          if (length(x) == 1) return(x)
          if (length(x) == 2) return(paste(x, collapse = " and "))
          paste0(paste(x[-length(x)], collapse = ", "), ", and ", x[length(x)])
        }
        
        # Add/normalize pronoun at the start of reason (and fix common conjugations)
        fmt_reason <- function(txt, n_routes) {
          s <- sub("\\.+$", "", trimws(txt))
          
          # Does the text start with a bare verb/adjective where a pronoun helps?
          needs_pronoun <- grepl(
            "^(could|would|should|can|cannot|can't|outside|exceed|exceeds|exceeded|violate|violates|violated|fit|fits|fitting|overlap|overlaps|overlapped|conflict|conflicts|fall|falls|do|does)\\b",
            s, ignore.case = TRUE
          )
          
          if (n_routes == 1) {
            s <- sub("^(?i)they\\b", "it", s, perl = TRUE)
            if (needs_pronoun && !grepl("^(?i)it\\b", s, perl = TRUE)) s <- paste("it", s)
            # Singular conjugations
            s <- sub("^(?i)it\\s+fall\\b", "it falls", s, perl = TRUE)
            s <- sub("^(?i)it\\s+do\\b",   "it does",  s, perl = TRUE)
            s <- gsub("(?i)\\bit do not\\b", "it does not", s, perl = TRUE)
            s <- gsub("(?i)\\bit are\\b",    "it is",       s, perl = TRUE)
            s <- sub("^(?i)it\\s+outside\\b", "it is outside", s, perl = TRUE)
          } else {
            s <- sub("^(?i)it\\b", "they", s, perl = TRUE)
            if (needs_pronoun && !grepl("^(?i)they\\b", s, perl = TRUE)) s <- paste("they", s)
            # Plural conjugations
            s <- sub("^(?i)they\\s+falls\\b", "they fall", s, perl = TRUE)
            s <- sub("^(?i)they\\s+outside\\b", "they are outside", s, perl = TRUE)
            s <- gsub("(?i)\\bthey does not\\b", "they do not", s, perl = TRUE)
            s <- gsub("(?i)\\bit would\\b", "they would", s, perl = TRUE)
            s <- gsub("(?i)\\bit is\\b",     "they are",  s, perl = TRUE)
          }
          s
        }
        
        groups <- split(df$urn, df$reason)
        
        grouped <- unlist(lapply(names(groups), function(rsn) {
          ids <- sort(as.integer(groups[[rsn]]))
          lead <- if (length(ids) == 1)
            sprintf("Route %s", ids)
          else
            sprintf("Routes %s", join_oxford_local(ids))
          sprintf("%s cannot be scheduled because %s.", lead, fmt_reason(rsn, length(ids)))
        }), use.names = FALSE)
        
        # Keep any lines that didn't match our pattern
        others <- unsched_msgs[!valid]
        unsched_msgs <- c(others, grouped)
      }
      # --- Post-filter: drop any per-day fragments for day labels whose aggregate cap is already reached ---
      # Compute caps-per-slot, then fold to caps-per-day (summing duplicate day labels if present)
      caps_by_slot <- sapply(seq_along(days), function(i) {
        v <- if (isTRUE(input$fine_tune_days)) nzint(input[[paste0("ft_surveys_", i)]]) else 40L
        if (!is.finite(v) || v <= 0L) 40L else v
      })
      caps_by_day <- tapply(caps_by_slot, days, sum)
      
      # Compute assigned-per-slot and fold to assigned-per-day
      assigned_by_slot <- sapply(seq_along(days), function(i) {
        df_i <- assignments[[i]]
        if (is.data.frame(df_i) && nrow(df_i)) sum(nzint(df_i[["Assigned Surveys"]]), na.rm = TRUE) else 0L
      })
      assigned_by_day <- tapply(assigned_by_slot, days, sum)
      
      closed_days <- names(caps_by_day)[assigned_by_day[names(caps_by_day)] >= caps_by_day]
      closed_days <- closed_days[is.finite(match(closed_days, names(caps_by_day)))]
      
      if (length(closed_days)) {
        # Clause-level filter: for each message, remove or rewrite any clause that references closed day labels.
        # - If a clause is specifically about caps ("already at its maximum" / "blocked by per-day cap") and mentions a closed day, drop the clause.
        # - Otherwise, remove the closed day tokens from the clause's day list (", Mon", " and Thu", etc.).
        #   If that leaves an "on" with no remaining day, drop the clause.
        day_pat <- paste0("\\b(", paste(unique(closed_days), collapse="|"), ")\\b")
        
        strip_closed_in_msg <- function(msg) {
          # Split head/body so we can rewrite only the reasons
          mm <- regexec("^(.*?\\bbecause\\s+)(.*)\\.$", msg, perl = TRUE)
          m  <- regmatches(msg, mm)[[1]]
          if (length(m) < 3) return(msg)  # not in expected format
          
          lead <- m[2]; reason_blob <- m[3]
          clauses <- unlist(strsplit(reason_blob, "\\s*\\|\\s*", perl = TRUE), use.names = FALSE)
          
          rewrite_clause <- function(cl) {
            cl2 <- trimws(cl)
            
            # Drop cap-specific clause mentioning a closed day entirely
            if (grepl(day_pat, cl2, perl = TRUE) &&
                grepl("already at its maximum|blocked by per-day cap", cl2, ignore.case = TRUE, perl = TRUE)) {
              return("")
            }
            
            # Remove closed day tokens from generic clauses (spacing/window/etc.)
            for (d in closed_days) {
              cl2 <- gsub(paste0("(,\\s*|\\s+(?:and|or)\\s+)?\\b", d, "\\b"), "", cl2, perl = TRUE)
            }
            
            # Cleanup punctuation around day lists
            cl2 <- gsub("\\s*,\\s*,+", ", ", cl2, perl = TRUE)
            cl2 <- gsub("\\s+(and|or)\\s*,", ", ", cl2, perl = TRUE)
            cl2 <- gsub(",\\s+(and|or)\\s*$", "", cl2, perl = TRUE)
            cl2 <- gsub("\\bon\\s*,", "on ", cl2, perl = TRUE)
            cl2 <- gsub(",\\s*(Sun|Mon|Tue|Wed|Thu|Fri|Sat)\\b\\s+on\\s", " on ", cl2, perl = TRUE)
            cl2 <- gsub("\\s{2,}", " ", cl2, perl = TRUE)
            cl2 <- trimws(cl2)
            
            # If original clause was day-specific ("on …") but no day remains, drop it
            had_on <- grepl("\\bon\\b", cl, perl = TRUE)
            has_day_now <- grepl("\\b(Sun|Mon|Tue|Wed|Thu|Fri|Sat)\\b", cl2, perl = TRUE)
            if (had_on && !has_day_now) return("")
            
            cl2
          }
          
          rewritten <- vapply(clauses, rewrite_clause, character(1), USE.NAMES = FALSE)
          rewritten <- rewritten[nzchar(rewritten)]
          if (!length(rewritten)) return("")  # drop the whole message
          paste0(lead, paste(rewritten, collapse = " | "), ".")
        }
        
        unsched_msgs <- vapply(unsched_msgs, strip_closed_in_msg, character(1), USE.NAMES = FALSE)
        unsched_msgs <- unsched_msgs[nzchar(unsched_msgs)]
      }
      
      # Plural grammar tweak for grouped lines (e.g., "Routes …"): "it does not" -> "they do not"
      unsched_msgs <- ifelse(grepl("^Routes\\b", unsched_msgs),
                             gsub("(?i)\\bit does not\\b", "they do not", unsched_msgs, perl = TRUE),
                             unsched_msgs)
      state$unscheduled_reasons <- unique(unsched_msgs)
      
      # --- Post-pass: ENFORCE max daily hours as a HARD constraint (Months 1–2; Month 3 only where Hard Limit is ON) ---
      
      # 1) Resolve per-slot caps (in hours) to minutes
      day_hours_caps_post <- sapply(seq_along(days), function(i){
        if (isTRUE(input$fine_tune_days)) {
          v <- nzint(input[[paste0("ft_hours_", i)]])
          if (!is.finite(v) || v <= 0L) 24L else v
        } else {
          v <- nzint(input$max_hours)
          if (!is.finite(v) || v <= 0L) 6L else v
        }
      })
      cap_mins_post <- as.integer(day_hours_caps_post) * 60L
      
      # Helper: choose the densest cap-length window for a set of assigned rows
      best_cap_window <- function(df_rows, cap_min) {
        if (!is.data.frame(df_rows) || !nrow(df_rows) || !is.finite(cap_min) || cap_min <= 0L) return(NULL)
        dep <- suppressWarnings(as.integer(df_rows$DepMin))
        S   <- nzint(df_rows[["Assigned Surveys"]])
        ok  <- is.finite(dep) & S > 0L
        if (!any(ok)) return(NULL)
        dep <- dep[ok]; S <- S[ok]
        xs  <- sort(unique(as.integer(dep)))
        best_start <- xs[1]; best_tot <- -Inf
        for (t in xs) {
          t2  <- t + cap_min
          tot <- sum(S[dep >= t & dep <= t2], na.rm = TRUE)
          if (tot > best_tot) { best_tot <- tot; best_start <- t }
        }
        list(start = as.integer(best_start), end = as.integer(best_start + cap_min))
      }
      
      # Decide which slots/days are hard-enforced right now
      month <- as.integer(input$month_index)
      hard_now <- vapply(seq_along(days), function(i){
        if (month %in% c(1L,2L)) {
          TRUE
        } else {
          isTRUE(hard_hours_flags[i])
        }
      }, logical(1))
      
      # 2) Aggregate by actual weekday label to prevent exceeding cap across duplicate slots
      uniq_days <- unique(as.character(days))
      
      for (dname in uniq_days) {
        idxs <- which(as.character(days) == dname & hard_now)
        if (!length(idxs)) next
        # If this weekday appears only once, there is nothing to "aggregate across slots".
        # Avoid post-clamping a single slot after scheduling (can create underfill + mismatched diagnostics).
        if (length(idxs) < 2L) next
        
        # Gather all assigned rows for this weekday across its slots
        all_rows <- NULL
        for (j in idxs) {
          df_j <- assignments[[j]]
          if (is.data.frame(df_j) && nrow(df_j)) {
            df_j$.__slot <- j
            all_rows <- if (is.null(all_rows)) df_j else suppressWarnings(dplyr::bind_rows(all_rows, df_j))
          }
        }
        if (is.null(all_rows) || !nrow(all_rows)) next
        
        # If already within the tightest cap across these slots, leave as-is
        s <- suppressWarnings(min(all_rows$DepMin, na.rm = TRUE))
        e <- suppressWarnings(max(all_rows$DepMin, na.rm = TRUE))
        if (is.finite(s) && is.finite(e)) {
          cap_min_day <- min(cap_mins_post[idxs], na.rm = TRUE)
          if ((e - s) <= cap_min_day) next
          
          # Pick densest window of length cap_min_day and clamp everything to it
          keep_win <- best_cap_window(all_rows, cap_min_day)
          if (!is.null(keep_win) && is.finite(keep_win$start) && is.finite(keep_win$end)) {
            kmin <- as.integer(keep_win$start)
            kmax <- as.integer(keep_win$end)
            
            for (j in idxs) {
              dj <- assignments[[j]]
              if (is.data.frame(dj) && nrow(dj)) {
                urn_trace <- as.integer(state$debug_urn %||% NA_integer_)
                had_trace <- FALSE
                if (is.finite(urn_trace) &&
                    "Unique Route Number" %in% names(dj) &&
                    "Assigned Surveys" %in% names(dj)) {
                  urnv_j <- suppressWarnings(as.integer(dj$`Unique Route Number`))
                  Sv_j   <- nzint(dj$`Assigned Surveys`)
                  had_trace <- any(is.finite(urnv_j) & urnv_j == urn_trace & Sv_j > 0L, na.rm = TRUE)
                }
                
                inside <- suppressWarnings(as.integer(dj$DepMin)) >= kmin &
                  suppressWarnings(as.integer(dj$DepMin)) <= kmax
                assignments[[j]] <- dj[inside, , drop = FALSE]
                
                if (isTRUE(had_trace)) {
                  df_after <- assignments[[j]]
                  still_trace <- FALSE
                  if (is.data.frame(df_after) && nrow(df_after) &&
                      "Unique Route Number" %in% names(df_after) &&
                      "Assigned Surveys" %in% names(df_after)) {
                    urnv_after <- suppressWarnings(as.integer(df_after$`Unique Route Number`))
                    Sv_after   <- nzint(df_after$`Assigned Surveys`)
                    still_trace <- any(is.finite(urnv_after) & urnv_after == urn_trace & Sv_after > 0L, na.rm = TRUE)
                  }
                  if (!still_trace) {
                    debug_note(
                      dname, j, "post_hours_drop_trace",
                      list(
                        trace_urn = urn_trace,
                        kmin      = as.integer(kmin),
                        kmax      = as.integer(kmax)
                      )
                    )
                  }
                }
              }
              # keep slot window in sync for diagnostics & later clamps
              slot_windows[[j]] <- list(start = kmin, end = kmax)
            }
          }
        }
      }
      
      # 3) Rebuild assigned_long from clamped per-slot assignments
      assigned_long <- {
        rows <- lapply(seq_along(assignments), function(j){
          df <- assignments[[j]]
          if (!is.data.frame(df) || !nrow(df)) return(NULL)
          # Ensure DepMin is present and normalized
          if (!("DepMin" %in% names(df))) {
            df$DepMin <- vapply(df$`Departure Time`, parse_user_time, integer(1))
          }
          df$DepMin <- ((as.integer(df$DepMin) %% 1440) + 1440) %% 1440
          df
        })
        suppressWarnings(dplyr::bind_rows(rows))
      }
      
      # Persist for any later use that expects slot_windows in state
      state$slot_windows <- slot_windows
      
      # --- End post-pass ---
      # --- Re-scale AM/PM caps to ACTUAL assigned total (Months 1–2) and trim if needed ---
      if (month %in% c(1L, 2L)) {
        tg <- get_targets()
        df <- assigned_long
        if (is.data.frame(df) && nrow(df)) {
          dep <- if ("DepMin" %in% names(df)) as.integer(df$DepMin) else vapply(df$`Departure Time`, parse_user_time, integer(1))
          dep <- ((dep %% 1440) + 1440) %% 1440
          is_am <- is.finite(dep) & dep < 12*60
          is_we <- df$Day %in% WEEKEND_DAYS
          total <- as.integer(sum(df$`Assigned Surveys`, na.rm = TRUE))
          if (!tg$split) {
            am_cap_act <- as.integer(floor(((tg$am_global + 10) / 100) * total))
            am_now     <- as.integer(sum(df$`Assigned Surveys`[is_am], na.rm = TRUE))
            over <- am_now - am_cap_act
            if (over > 0L) {
              idx <- which(is_am & df$`Assigned Surveys` > 0L)
              if (length(idx)) {
                ord <- idx[order(df$`Assigned Surveys`[idx], decreasing = TRUE)]
                
                # Keep a per-day tally so trimming never drops any day below 30 in Months 1–2
                per_day_now <- tapply(df$`Assigned Surveys`, df$Day, sum, na.rm = TRUE)
                per_day_now[is.na(per_day_now)] <- 0L
                
                for (j in ord) {
                  if (over <= 0L) break
                  dj <- as.character(df$Day[j])
                  room_day <- as.integer(max(0L, (per_day_now[[dj]] %||% 0L) - 30L))
                  if (room_day <= 0L) next
                  dec <- min(as.integer(df$`Assigned Surveys`[j]),
                             as.integer(over),
                             as.integer(room_day))
                  if (dec <= 0L) next
                  df$`Assigned Surveys`[j] <- as.integer(df$`Assigned Surveys`[j] - dec)
                  per_day_now[[dj]] <- as.integer((per_day_now[[dj]] %||% 0L) - dec)
                  over <- as.integer(over - dec)
                }
              }
            }
          } else {
            # Separate weekday/weekend caps, scaled to actual WD/WE totals
            tot_wd <- as.integer(sum(df$`Assigned Surveys`[!is_we], na.rm = TRUE))
            tot_we <- as.integer(sum(df$`Assigned Surveys`[ is_we], na.rm = TRUE))
            am_wd_cap_act <- as.integer(floor(((tg$am_wd + 10) / 100) * pmax(0L, tot_wd)))
            am_we_cap_act <- as.integer(floor(((tg$am_we + 10) / 100) * pmax(0L, tot_we)))
            am_wd_now <- as.integer(sum(df$`Assigned Surveys`[!is_we & is_am], na.rm = TRUE))
            am_we_now <- as.integer(sum(df$`Assigned Surveys`[ is_we & is_am], na.rm = TRUE))
            # Reduce Weekday AM overage — but never drop any single day below 30 total
            over <- am_wd_now - am_wd_cap_act
            if (over > 0L) {
              idx <- which(!is_we & is_am & df$`Assigned Surveys` > 0L)
              ord <- idx[order(df$`Assigned Surveys`[idx], decreasing = TRUE)]
              
              # Mutable per-day floor guard
              per_day_now <- tapply(df$`Assigned Surveys`, df$Day, sum, na.rm = TRUE)
              per_day_now[is.na(per_day_now)] <- 0L
              
              for (j in ord) {
                if (over <= 0L) break
                dj <- as.character(df$Day[j])
                room_day <- as.integer(max(0L, (per_day_now[[dj]] %||% 0L) - 30L))
                if (room_day <= 0L) next
                dec <- min(as.integer(df$`Assigned Surveys`[j]),
                           as.integer(over),
                           as.integer(room_day))
                if (dec <= 0L) next
                df$`Assigned Surveys`[j] <- as.integer(df$`Assigned Surveys`[j] - dec)
                per_day_now[[dj]] <- as.integer((per_day_now[[dj]] %||% 0L) - dec)
                over <- as.integer(over - dec)
              }
            }
            # Reduce Weekend AM overage — but never drop any single day below 30 total
            over <- am_we_now - am_we_cap_act
            if (over > 0L) {
              idx <- which(is_we & is_am & df$`Assigned Surveys` > 0L)
              ord <- idx[order(df$`Assigned Surveys`[idx], decreasing = TRUE)]
              
              # Build mutable per-day tally to enforce floor while trimming
              per_day_now <- tapply(df$`Assigned Surveys`, df$Day, sum, na.rm = TRUE)
              per_day_now[is.na(per_day_now)] <- 0L
              
              for (j in ord) {
                if (over <= 0L) break
                dj <- as.character(df$Day[j])
                room_day <- as.integer(max(0L, (per_day_now[[dj]] %||% 0L) - 30L))
                if (room_day <= 0L) next
                dec <- min(as.integer(df$`Assigned Surveys`[j]),
                           as.integer(over),
                           as.integer(room_day))
                if (dec <= 0L) next
                df$`Assigned Surveys`[j] <- as.integer(df$`Assigned Surveys`[j] - dec)
                per_day_now[[dj]] <- as.integer((per_day_now[[dj]] %||% 0L) - dec)
                over <- as.integer(over - dec)
              }
            }
          }
          assigned_long <- df
          # --- Sync AM/PM trim back into per-slot schedules so per-day totals match header ---
          if (is.list(assignments) && is.data.frame(assigned_long)) {
            # Build a simple join key present in both frames
            mk_key <- function(x, fallback_day = NULL) {
              depm <- if ("DepMin" %in% names(x)) as.integer(x[["DepMin"]]) else {
                suppressWarnings(parse_user_time(as.character(x[["Departure Time"]] %||% NA_character_)))
              }
              paste0(
                as.character(x[["Day"]] %||% fallback_day),
                "|", as.integer(x[["Unique Route Number"]] %||% NA_integer_),
                "|", as.character(x[["Flight #"]] %||% NA_character_),
                "|", as.character(x[["Departure Time"]] %||% NA_character_),
                "|", as.integer(depm)
              )
            }
            al <- assigned_long
            al$key <- mk_key(al)
            
            for (ii in seq_along(assignments)) {
              df_i <- assignments[[ii]]
              if (!is.data.frame(df_i) || !nrow(df_i)) next
              df_i$key <- mk_key(df_i, fallback_day = as.character(df_i$Day[1]))
              
              # Pull trimmed counts; missing -> 0
              mapped <- merge(df_i, al[, c("key","Assigned Surveys")],
                              by = "key", all.x = TRUE, suffixes = c("", ".trim"))
              mapped$`Assigned Surveys` <- as.integer(tidyr::replace_na(mapped$`Assigned Surveys.trim`, 0L))
              mapped$`Assigned Surveys.trim` <- NULL
              mapped$key <- NULL
              assignments[[ii]] <- mapped
            }
          }
        }
        # --- Floor Filler (Months 1–2): make sure each selected day has at least 30 assigned ---
        # Runs after AM/PM trim and after syncing back to per-slot schedules.
        min_floor <- 30L
        cap_pf    <- as.integer(nzint(input$per_flight_cap %||% 10L))
        
        # Helper: join key (reuse same shape as sync code above)
        mk_key <- function(x, fallback_day = NULL) {
          depm <- if ("DepMin" %in% names(x)) as.integer(x[["DepMin"]]) else {
            suppressWarnings(parse_user_time(as.character(x[["Departure Time"]] %||% NA_character_)))
          }
          paste0(
            as.character(x[["Day"]] %||% fallback_day),
            "|", as.integer(x[["Unique Route Number"]] %||% NA_integer_),
            "|", as.character(x[["Flight #"]] %||% NA_character_),
            "|", as.character(x[["Departure Time"]] %||% NA_character_),
            "|", as.integer(depm)
          )
        }
        
        # Current totals per slot (after trim/sync)
        per_day_now <- vapply(seq_along(assignments), function(i) {
          x <- assignments[[i]]
          if (is.data.frame(x) && nrow(x)) sum(x$`Assigned Surveys`, na.rm = TRUE) else 0L
        }, integer(1))
        
        # Route remaining map = route_base$remaining minus what's in assigned_long (post-trim)
        assigned_by_urn <- if (is.data.frame(assigned_long) && nrow(assigned_long)) {
          aggregate(assigned_long$`Assigned Surveys`,
                    list(assigned_long$`Unique Route Number`), sum)
        } else data.frame(Group.1 = integer(0), x = integer(0))
        rem_map <- setNames(
          pmax(
            0L,
            route_base$remaining -
              (assigned_by_urn$x[match(route_base$`Unique Route Number`, assigned_by_urn$Group.1)] %||% 0L)
          ),
          route_base$`Unique Route Number`
        )
        
        al_keys <- if (is.data.frame(assigned_long) && nrow(assigned_long)) mk_key(assigned_long) else character(0)
        
        for (i in seq_along(assignments)) {
          need <- as.integer(min_floor - (per_day_now[[i]] %||% 0L))
          if (need <= 0L) next
          
          d <- as.character(days[[i]] %||% NA_character_)
          if (!nzchar(d)) next
          
          # Candidate flights on this day not already scheduled
          cand <- df[df$Day == d, , drop = FALSE]
          if (!nrow(cand)) next
          cand$key <- mk_key(cand, fallback_day = d)
          cand <- cand[!(cand$key %in% al_keys), , drop = FALSE]
          if (!nrow(cand)) next
          
          # Respect hard hours if toggled by the user (do NOT force by month)
          if (isTRUE(input$hard_earliest)) {
            cap_min <- parse_user_time(input$earliest_dep)
            if (is.finite(cap_min)) cand <- cand[as.integer(cand$DepMin) >= cap_min, , drop = FALSE]
          }
          if (isTRUE(input$hard_latest)) {
            cap_max <- parse_user_time(input$latest_dep)
            if (is.finite(cap_max)) cand <- cand[as.integer(cand$DepMin) <= cap_max, , drop = FALSE]
          }
          if (!nrow(cand)) next
          
          # How many surveys remain per URN (post-trim)
          cand$rem <- rem_map[match(as.integer(cand$`Unique Route Number`), as.integer(names(rem_map)))]
          cand$rem[is.na(cand$rem)] <- 0L
          cand <- cand[cand$rem > 0L, , drop = FALSE]
          if (!nrow(cand)) next
          
          # Greedy: favor higher remaining (infrequent benefit), then earlier departures
          ord <- order(-cand$rem, as.integer(cand$DepMin), cand$Airline, cand$Destination, na.last = TRUE)
          cand <- cand[ord, , drop = FALSE]
          
          # Add rows until we hit the floor or run out
          need_left <- as.integer(need)
          add_rows  <- list()
          for (r in seq_len(nrow(cand))) {
            if (need_left <= 0L) break
            urn <- as.integer(cand$`Unique Route Number`[r])
            rem <- as.integer(cand$rem[r])
            if (rem <= 0L) next
            at_most <- as.integer(min(cap_pf, rem, need_left))
            if (at_most <= 0L) next
            
            row <- cand[r, , drop = FALSE]
            row$`Assigned Surveys` <- at_most
            
            # Keep only columns present in assigned_long so the bind_rows is clean
            keep_cols <- intersect(names(row), names(assigned_long))
            add_rows[[length(add_rows) + 1L]] <- row[, keep_cols, drop = FALSE]
            
            # Update trackers
            rem_map[[as.character(urn)]] <- max(0L, rem - at_most)
            need_left <- as.integer(need_left - at_most)
          }
          
          if (length(add_rows)) {
            extra <- dplyr::bind_rows(add_rows)
            assigned_long <- dplyr::bind_rows(assigned_long, extra)
            # also update slot schedule and totals
            assignments[[i]] <- dplyr::bind_rows(assignments[[i]] %||% assigned_long[0, ], extra) %>%
              dplyr::arrange(DepMin, Concourse, Airline)
            per_day_now[[i]] <- as.integer(per_day_now[[i]] + sum(extra$`Assigned Surveys`, na.rm = TRUE))
            # extend anti-duplication keys for subsequent slots
            al_keys <- c(al_keys, mk_key(extra, fallback_day = d))
          }
        }
      }
      
      # ---- Save state & tables ---------------------------------------------
      state$day_list      <- days
      state$schedules     <- assignments
      state$assigned_long <- assigned_long
      state$summary       <- list(per_day_totals = setNames(sapply(assignments, function(x) if (nrow(x)) sum(x$`Assigned Surveys`) else 0L), days))
      # Build slot-aware spacing-bypass chains from the final schedules
      spacing_chains <- compute_spacing_chains(assignments, days)
      
      state$bypassed <- list(
        spacing_pairs      = bypass_acc$spacing_pairs %||% list(),  # kept for fallback
        spacing_chains     = spacing_chains,                        # NEW preferred structure
        daily_hours_days   = sort(unique(bypass_acc$daily_hours_days %||% character(0))),
        after_latest_count = classify_bins(assigned_long, earliest_cap_min = parse_user_time(input$earliest_dep %||% "6:00 AM"), latest_cap_min = state$latest_cap_min)$after_cap_flights %||% 0L
      )
      
      # Updated Routes Remaining table
      state$routes_updated <- routes_updated
      
      # “Required Routes with No Flights” (renamed tab content)
      nf_tbl <- if (is.null(nf)) tibble::tibble(Message="No 'Required Routes with No Flights' sheet found.") else {
        nf %>% dplyr::arrange(`Unique Route Number`)
      }
      state$nf_tbl <- nf_tbl
      state$has_run_generate <- TRUE
      
      cat("=== GENERATE END (OK) ===\n")
      
    }, error = function(e){
      # Surface the real error both in UI and console
      msg <- conditionMessage(e)
      showNotification(paste("Generate failed:", msg), type = "error", duration = 12)
      cat("\n*** GENERATE FAILED ***\n", msg, "\n")
      cat("Trace:\n"); print(sys.calls())
      stop(e)  # rethrow for console traceback
    })
  })
  
  # ---------------------- Dynamic tabs ----------------------
  output$mainTabsUI <- renderUI({
    days <- state$day_list %||% selected_days()
    n <- length(days); day_tabs <- vector("list", n)
    for (i in seq_len(n)) day_tabs[[i]] <- tabPanel(paste0("Day ", i), DTOutput(paste0("day", i, "_tbl")))
    panels <- c(
      list(tabPanel("Summary / Diagnostics", br(), uiOutput("summary_banner"), br(), DTOutput("summary_table"))),
      day_tabs,
      list(
        tabPanel("Updated Routes Remaining", DTOutput("routes_remaining_tbl")),
        tabPanel("Surveys Completed", DTOutput("surveys_completed_tbl")),
        tabPanel("Date Fit Summary",            DTOutput("fit_tbl")),
        tabPanel("Required Routes with No Flights", DTOutput("routes_unable_tbl")),
        tabPanel(
          "Debug Trace",
          fluidRow(
            column(
              4,
              numericInput(
                "debug_urn",
                "Trace Unique Route Number (URN) in Debug:",
                value = NA,
                min = 1,
                step = 1
              )
            )
          ),
          DTOutput("debug_tbl")
        )
      )
    )
    do.call(tabsetPanel, c(list(id="mainTabs"), panels))
  })
  
  # ---------------------- UI renderers ----------------------
  output$summary_banner <- renderUI({
    if (!isTRUE(state$has_run_generate %||% FALSE)) return(NULL)
    assigned_now <- state$assigned_long %||% tibble()
    days <- state$day_list %||% character(0)
    per_day_totals <- state$summary$per_day_totals %||% rep(0L, length(days))
    bins <- classify_bins(assigned_now, earliest_cap_min = parse_user_time(input$earliest_dep %||% "6:00 AM"), latest_cap_min = state$latest_cap_min)
    total_assigned <- sum(assigned_now[["Assigned Surveys"]] %||% integer(0), na.rm = TRUE)
    after_latest_count <- bins$after_cap_flights %||% 0L
    cap_label <- mins_to_ampm(state$latest_cap_min %||% parse_user_time(input$latest_dep %||% "8:45 PM"))
    pre6 <- bins$pre6_flights %||% 0L
    month <- as.integer(input$month_index %||% 1L)
    
    pills <- list(
      tags$div(style="background:#f7f7f7;border-radius:10px;padding:10px 14px;",
               tags$b("Total Surveys Assigned:"), paste0(total_assigned)),
      tags$div(style="background:#f7f7f7;border-radius:10px;padding:10px 14px;",
               tags$b("Per-day totals:"), if (length(days)) paste(paste0(days, " (", seq_along(days), ")=", per_day_totals[seq_along(days)]), collapse=", ") else "—"),
      tags$div(style="background:#f7f7f7;border-radius:10px;padding:10px 14px;",
               tags$b("Weekday AM Assigned:"), bins$wd_am),
      tags$div(style="background:#f7f7f7;border-radius:10px;padding:10px 14px;",
               tags$b("Weekday PM Assigned:"), bins$wd_pm),
      tags$div(style="background:#f7f7f7;border-radius:10px;padding:10px 14px;",
               tags$b("Weekend AM Assigned:"), bins$we_am),
      tags$div(style="background:#f7f7f7;border-radius:10px;padding:10px 14px;",
               tags$b("Weekend PM Assigned:"), bins$we_pm)
    )
    # Warnings: only show if counts > 1 and reflect input times
    if ((after_latest_count %||% 0L) > 1L) {
      pills <- append(pills, list(
        tags$div(style="background:#fbe9e7;border-radius:10px;padding:10px 14px;",
                 tags$b("Flights assigned after "), tags$b(cap_label), tags$b(":"), after_latest_count)
      ))
    }
    earliest_label <- mins_to_ampm(parse_user_time(input$earliest_dep %||% "6:00 AM"))
    if ((pre6 %||% 0L) > 1L) {
      pills <- append(pills, list(
        tags$div(style="background:#fffde7;border-radius:10px;padding:10px 14px;",
                 tags$b("Flights scheduled before "), tags$b(earliest_label), tags$b(":"), pre6)
      ))
    }
    
    # --- Warning/diagnostic messages (Summary banner) ---
    yellow_msgs <- character(0)
    
    # Date-fit auto-repair notes (soft)
    if (length(state$datefit_repairs %||% character(0))) {
      yellow_msgs <- c(yellow_msgs, state$datefit_repairs)
    }
    
    # Spacing chains & daily-hours (soft)
    bp <- state$bypassed %||% list()
    
    # Prefer chain-style spacing messages keyed by slot label, else fall back to old pairs-by-weekday
    if (is.list(bp$spacing_chains) && length(bp$spacing_chains)) {
      nm <- names(bp$spacing_chains) %||% character(0)
      slot_ord <- suppressWarnings(as.integer(sub(".*\\((\\d+)\\).*", "\\1", nm)))
      ord <- order(ifelse(is.na(slot_ord), seq_along(nm), slot_ord))
      for (k in nm[ord]) {
        chains <- unique(as.character(bp$spacing_chains[[k]] %||% character(0)))
        if (length(chains)) {
          yellow_msgs <- c(
            yellow_msgs,
            sprintf("Routes bypassing interflight spacing on %s: %s", k, paste(chains, collapse = "; "))
          )
        }
      }
    } else if (is.list(bp$spacing_pairs) && length(bp$spacing_pairs)) {
      for (dy in DAY_LEVELS) {
        pairs <- unique(as.character((bp$spacing_pairs[[dy]] %||% character(0))))
        if (length(pairs)) {
          yellow_msgs <- c(
            yellow_msgs,
            sprintf("Routes bypassing interflight spacing on %s: %s", dy, paste(pairs, collapse = ", "))
          )
        }
      }
    }
    
    # Daily-hours exceeded: prefer slot-tagged labels like "Sun (1)"; drop plain duplicates like "Sun"
    if (length(bp$daily_hours_days %||% character(0)) > 0) {
      dh <- unique(as.character(bp$daily_hours_days))
      plain  <- dh[!grepl("\\(", dh)]
      tagged <- dh[grepl("\\(", dh)]
      base_days <- sub("\\s*\\(.*\\)$", "", tagged)
      keep <- c(tagged, setdiff(plain, base_days))
      if (length(keep)) {
        yellow_msgs <- c(
          yellow_msgs,
          sprintf("Maximum daily hours exceeded on day(s): %s.", paste(sort(keep), collapse = ", "))
        )
      }
    }
    
    # Build boxes
    yellow_box <- NULL
    if (length(yellow_msgs) > 0) {
      yellow_box <- tags$div(
        style=paste0("background:", SOFT_COLOR, ";border-radius:10px;padding:10px 14px;"),
        tags$b("Soft constraints overridden to build schedule:"),
        tags$ul(lapply(unique(yellow_msgs), function(t) tags$li(t)))
      )
    }
    
    red_box <- NULL
    if (!is.null(state$unscheduled_reasons) && length(state$unscheduled_reasons) > 0) {
      red_box <- tags$div(
        style=paste0("background:",HARD_COLOR,";border-radius:10px;padding:10px 14px;"),
        tags$b("Unable to Assign All Surveys"),
        tags$ul(lapply(unique(state$unscheduled_reasons), function(t) tags$li(t)))
      )
    }
    
    tags$div(
      style="display:flex; flex-direction:column; gap:14px;",
      tags$div(style="display:flex; gap:18px; flex-wrap:wrap;", pills),
      if (!is.null(yellow_box)) yellow_box,
      red_box
    )
  })
  
  output$fit_tbl <- DT::renderDT({
    fit <- state$date_fit
    if (is.null(fit) || !nrow(fit)) {
      return(DT::datatable(as_plain_df(data.frame(Message="No schedules yet.")), options = list(dom = 't'), rownames = FALSE))
    }
    DT::datatable(as_plain_df(fit), options = list(pageLength = 10, autoWidth = TRUE, dom='tip'), rownames = FALSE)
  })
  
  output$summary_table <- renderDT({
    if (is.null(state$assigned_long) || is.null(state$day_list)) {
      return(DT::datatable(
        as_plain_df(data.frame(Message = "No schedule yet. Click Generate.", stringsAsFactors = FALSE)),
        options = list(pageLength = 7, dom = 'tip'), rownames = FALSE
      ))
    }
    assigned_now <- state$assigned_long
    days <- state$day_list %||% character(0)
    
    # Header (overall totals)
    bins <- classify_bins(assigned_now, earliest_cap_min = parse_user_time(input$earliest_dep %||% "6:00 AM"), latest_cap_min = (state$latest_cap_min %||% parse_user_time(input$latest_dep)))
    header <- data.frame(
      Day = "Total",
      `Assigned Total` = sum(assigned_now[["Assigned Surveys"]] %||% integer(0), na.rm = TRUE),
      `AM Assigned`    = (bins$wd_am %||% 0L) + (bins$we_am %||% 0L),
      `PM Assigned`    = (bins$wd_pm %||% 0L) + (bins$we_pm %||% 0L),
      stringsAsFactors = FALSE, check.names = FALSE
    )
    
    # Per-slot rows (keep duplicates distinct: "Sun (1)", "Sun (4)")
    per_slot_rows <- lapply(seq_along(days), function(i) {
      df_i <- if (i >= 1L && i <= length(state$schedules)) state$schedules[[i]] else NULL
      if (!is.data.frame(df_i) || nrow(df_i) == 0) {
        data.frame(
          Day = paste0(days[i], " (", i, ")"),
          `Assigned Total` = 0L,
          `AM Assigned`    = 0L,
          `PM Assigned`    = 0L,
          stringsAsFactors = FALSE, check.names = FALSE
        )
      } else {
        am <- sum(df_i$`Assigned Surveys`[is.finite(df_i$DepMin) & df_i$DepMin < 12*60], na.rm = TRUE)
        pm <- sum(df_i$`Assigned Surveys`[is.finite(df_i$DepMin) & df_i$DepMin >= 12*60], na.rm = TRUE)
        data.frame(
          Day = paste0(days[i], " (", i, ")"),
          `Assigned Total` = as.integer(sum(df_i$`Assigned Surveys`, na.rm = TRUE)),
          `AM Assigned`    = as.integer(am),
          `PM Assigned`    = as.integer(pm),
          stringsAsFactors = FALSE, check.names = FALSE
        )
      }
    })
    
    out <- dplyr::bind_rows(list(header, dplyr::bind_rows(per_slot_rows)))
    DT::datatable(as_plain_df(out), options = list(pageLength = 7, dom = 'tip'), rownames = FALSE)
  })
  
  output$routes_remaining_tbl <- renderDT({
    df <- state$routes_updated
    if (is.null(df)) return(DT::datatable(as_plain_df(data.frame()), options = list(dom='t'), rownames = FALSE))
    keep <- c("Airline","Destination","Assigned Surveys","Flight Type","Airline Code","Destination Code","Unique Route Number","Days of Operation")
    keep <- intersect(keep, names(df))
    DT::datatable(as_plain_df(select(df, all_of(keep))), options = list(pageLength = 20, autoWidth = TRUE), rownames = FALSE)
  })
  
  output$routes_unable_tbl <- renderDT({
    df <- state$nf_tbl
    if (is.null(df)) return(DT::datatable(as_plain_df(data.frame()), options = list(dom='t'), rownames = FALSE))
    keep <- c("Airline","Destination","Assigned Surveys","Flight Type","Airline Code","Destination Code","Unique Route Number","Message")
    keep <- intersect(keep, names(df))
    DT::datatable(as_plain_df(select(df, all_of(keep))), options = list(pageLength = 20, autoWidth = TRUE), rownames = FALSE)
  })
  
  output$surveys_completed_tbl <- DT::renderDT({
    df <- state$assigned_long
    if (is.null(df) || !is.data.frame(df) || !nrow(df)) {
      return(DT::datatable(as_plain_df(data.frame()), options = list(dom = 't'), rownames = FALSE))
    }
    
    # Join Days of Operation like before
    rr_local <- routes_remaining()
    codes_from_rr <- rr_local %>%
      dplyr::select(`Unique Route Number`, `Days of Operation`) %>%
      dplyr::distinct()
    df2 <- df %>% dplyr::left_join(codes_from_rr, by = "Unique Route Number")
    
    # Normalize Departure Time to AM/PM (prefer DepMin if present)
    if ("DepMin" %in% names(df2)) {
      df2[["Departure Time"]] <- vapply(as.integer(df2$DepMin), mins_to_ampm, character(1))
    } else if ("Departure Time" %in% names(df2)) {
      tt_min <- vapply(as.character(df2[["Departure Time"]]), parse_user_time, integer(1))
      df2[["Departure Time"]] <- vapply(tt_min, mins_to_ampm, character(1))
    }
    
    keep <- c(
      "Day","Airline","Concourse","Destination","Flight #","Departure Time",
      "Assigned Surveys","Flight Type","Airline Code","Destination Code",
      "Unique Route Number","Days of Operation"
    )
    keep <- intersect(keep, names(df2))
    
    DT::datatable(
      as_plain_df(dplyr::select(df2, dplyr::all_of(keep))),
      options = list(pageLength = 25, autoWidth = TRUE),
      rownames = FALSE
    )
  })
  output$debug_tbl <- DT::renderDT({
    rows <- state$debug %||% list()
    if (!length(rows)) {
      return(
        DT::datatable(
          as_plain_df(data.frame(Message = "No debug trace yet. Click Generate.")),
          options = list(dom = 't'),
          rownames = FALSE
        )
      )
    }
    # Standardize keys across variably-shaped entries
    keys <- unique(unlist(lapply(rows, names)))
    if (is.null(keys) || !length(keys)) keys <- c("Day","Slot","Step")
    mat <- lapply(rows, function(x) {
      out <- setNames(as.list(rep(NA_character_, length(keys))), keys)
      for (nm in names(x)) out[[nm]] <- as.character(x[[nm]])
      out
    })
    df <- as_plain_df(dplyr::bind_rows(mat))
    DT::datatable(df, options = list(pageLength = 25, autoWidth = TRUE), rownames = FALSE)
  })
  
  # ---- Day tables (Gate kept only in day sheets) ----
  for (i in 1:4) local({
    idx <- i
    output[[paste0("day", idx, "_tbl")]] <- DT::renderDT({
      tryCatch({
        df <- if (!is.null(state$schedules) && idx >= 1L && idx <= length(state$schedules)) state$schedules[[idx]] else NULL
        if (!is.data.frame(df) || nrow(df) == 0) {
          return(DT::datatable(as_plain_df(data.frame()), options = list(dom = 't'), rownames = FALSE))
        }
        df <- dplyr::arrange(df, DepMin)
        
        # Ensure 12-hour AM/PM time in schedules
        if ("DepMin" %in% names(df)) {
          df[["Departure Time"]] <- vapply(as.integer(df$DepMin), mins_to_ampm, character(1))
        } else if ("Departure Time" %in% names(df)) {
          tt_min <- vapply(as.character(df[["Departure Time"]]), parse_user_time, integer(1))
          df[["Departure Time"]] <- vapply(tt_min, mins_to_ampm, character(1))
        }
        
        day_label <- (state$day_list %||% character(0))[idx]
        if (is.null(day_label) || is.na(day_label) || !nzchar(day_label)) day_label <- ""
        df$Date <- as.character(day_label)
        
        # Reorder columns explicitly, then coerce to a plain df to avoid JS “[object Object]”
        keep_order <- c("Date","Airline","Destination","Departure Time","Assigned Surveys","Concourse","Flight Type","Gate","Airline Code","Destination Code")
        df <- df %>%
          dplyr::select(dplyr::any_of(c(keep_order, "Unique Route Number","DepMin"))) %>%
          dplyr::select(dplyr::any_of(keep_order))
        
        DT::datatable(as_plain_df(df), options = list(pageLength = 20, autoWidth = TRUE), rownames = FALSE)
      }, error = function(e) {
        DT::datatable(as_plain_df(data.frame(Error = conditionMessage(e))), options = list(dom = 't'), rownames = FALSE)
      })
    })
  })
  
  export_basename <- reactive({
    df <- flights_df()
    days <- selected_days()
    dates <- df$dep_date[df$Day %in% days]
    
    if (isTRUE(input$restrict_dates_master)) {
      slot_labels <- c(input$day1, input$day2, input$day3, input$day4)
      slot_idx    <- which(slot_labels %in% DAY_LEVELS)
      allowed <- unlist(lapply(slot_idx, function(slot_no) {
        as.Date(input[[paste0("dates_slot", slot_no)]] %||% character(0))
      }))
      allowed <- allowed[!is.na(allowed)]
      if (length(allowed)) dates <- intersect(dates, allowed)
    }
    
    if (!length(dates)) dates <- df$dep_date
    ym <- sort(unique(lubridate::floor_date(dates, "month")))
    idx <- as.integer(input$month_index %||% 1L)
    pick <- if (length(ym) >= idx) ym[idx] else ym[length(ym)]
    sprintf("Airport_Survey_Schedule_%s_%s", format(pick, "%Y"), format(pick, "%b"))
  })
  
  # ---------------------- Download ----------------------
  output$download <- downloadHandler(
    filename = function() {
      d <- tryCatch({
        df <- flights_df()
        if (!is.null(df) && "dep_date" %in% names(df)) {
          suppressWarnings(max(as.Date(df$dep_date), na.rm = TRUE))
        } else Sys.Date()
      }, error = function(e) Sys.Date())
      if (is.na(d) || !is.finite(as.numeric(d))) d <- Sys.Date()
      y <- format(d, "%Y")
      m <- format(d, "%b")  # "Sep"
      sprintf("Airport_Survey_Schedule_%s_%s.xlsx", y, m)
    },
    contentType = "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
    content = function(file) {
      to_excel_df <- function(x) {
        if (is.null(x)) return(data.frame())
        if (!is.data.frame(x)) x <- as.data.frame(x, stringsAsFactors = FALSE)
        for (nm in names(x)) {
          col <- x[[nm]]
          if (is.list(col) && !is.data.frame(col)) {
            simple <- vapply(col, function(v) length(v) <= 1, logical(1))
            if (all(simple)) x[[nm]] <- vapply(col, function(v) if (length(v)) as.character(v[[1]]) else "", character(1))
            else x[[nm]] <- vapply(col, function(v) paste(as.character(v), collapse = ", "), character(1))
          }
        }
        x
      }
      safe_ncol <- function(x) if (!is.data.frame(x) || is.null(x) || is.na(ncol(x)) || ncol(x) < 1) 1L else ncol(x)
      
      wb   <- openxlsx::createWorkbook()
      days <- state$day_list
      
      # ---------- Summary & Diagnostics (FIRST sheet, NO freeze) ----------
      openxlsx::addWorksheet(wb, "Summary & Diagnostics")
      openxlsx::setColWidths(wb, sheet = "Summary & Diagnostics", cols = 1, widths = 25)
      
      assigned_now <- state$assigned_long %||% tibble::tibble()
      bins <- classify_bins(assigned_now, earliest_cap_min = parse_user_time(input$earliest_dep %||% "6:00 AM"), latest_cap_min = state$latest_cap_min)
      total_assigned <- sum(assigned_now[["Assigned Surveys"]] %||% integer(0), na.rm = TRUE)
      cap_label <- mins_to_ampm(state$latest_cap_min %||% parse_user_time(input$latest_dep %||% "8:45 PM"))
      after_latest_count <- bins$after_cap_flights %||% 0L
      month <- as.integer(input$month_index %||% 1L)
      
      # Build yellow (soft) + red (hard) messages
      yellow_msgs <- character(0)
      if (!isTRUE(input$hard_latest) && (after_latest_count %||% 0L) > 0) {
        yellow_msgs <- c(yellow_msgs, sprintf("Scheduled %d flight(s) after the latest time cap (%s).", after_latest_count, cap_label))
      }
      if (length(state$datefit_repairs %||% character(0))) {
        yellow_msgs <- c(yellow_msgs, state$datefit_repairs)
      }
      bp <- state$bypassed %||% list()
      
      # Spacing chains by slot (preferred)
      if (is.list(bp$spacing_chains) && length(bp$spacing_chains)) {
        nm <- names(bp$spacing_chains) %||% character(0)
        slot_ord <- suppressWarnings(as.integer(sub(".*\\((\\d+)\\).*", "\\1", nm)))
        ord <- order(ifelse(is.na(slot_ord), seq_along(nm), slot_ord))
        for (k in nm[ord]) {
          chains <- unique(as.character(bp$spacing_chains[[k]] %||% character(0)))
          if (length(chains)) {
            yellow_msgs <- c(yellow_msgs, sprintf("Routes bypassing interflight spacing on %s: %s", k, paste(chains, collapse = "; ")))
          }
        }
      }
      
      # Daily-hours exceeded (dedupe plain vs slot-tagged)
      if (length(bp$daily_hours_days %||% character(0)) > 0) {
        dh <- unique(as.character(bp$daily_hours_days))
        plain  <- dh[!grepl("\\(", dh)]
        tagged <- dh[grepl("\\(", dh)]
        base_days <- sub("\\s*\\(.*\\)$", "", tagged)
        keep <- c(tagged, setdiff(plain, base_days))  # drop "Sun" if "Sun (1)" exists
        if (length(keep)) {
          yellow_msgs <- c(yellow_msgs, sprintf("Maximum daily hours exceeded on day(s): %s.", paste(sort(keep), collapse = ", ")))
        }
      }
      
      red_msgs <- unique(state$unscheduled_reasons %||% character(0))
      
      # Write yellow & red boxes (as tables)
      r <- 1L
      if (length(yellow_msgs)) {
        ym_df <- data.frame(`Soft constraints overridden` = yellow_msgs, check.names = FALSE, stringsAsFactors = FALSE)
        openxlsx::writeData(wb, "Summary & Diagnostics", to_excel_df(ym_df), startRow = r, keepNA = FALSE)
        r <- r + nrow(ym_df) + 2L
      }
      if (length(red_msgs)) {
        rm_df <- data.frame(`Unable to assign reasons` = red_msgs, check.names = FALSE, stringsAsFactors = FALSE)
        openxlsx::writeData(wb, "Summary & Diagnostics", to_excel_df(rm_df), startRow = r, keepNA = FALSE)
        r <- r + nrow(rm_df) + 2L
      }
      
      # Summary table (Total + per-slot)
      days_vec <- days %||% character(0)
      per_slot_rows <- lapply(seq_along(days_vec), function(i) {
        df_i <- if (i >= 1L && i <= length(state$schedules)) state$schedules[[i]] else NULL
        if (!is.data.frame(df_i) || nrow(df_i) == 0) {
          data.frame(
            Day = paste0(days_vec[i], " (", i, ")"),
            `Assigned Total` = 0L,
            `AM Assigned` = 0L,
            `PM Assigned` = 0L,
            check.names = FALSE, stringsAsFactors = FALSE
          )
        } else {
          am <- sum(df_i$`Assigned Surveys`[is.finite(df_i$DepMin) & df_i$DepMin < 12*60], na.rm = TRUE)
          pm <- sum(df_i$`Assigned Surveys`[is.finite(df_i$DepMin) & df_i$DepMin >= 12*60], na.rm = TRUE)
          data.frame(
            Day = paste0(days_vec[i], " (", i, ")"),
            `Assigned Total` = as.integer(sum(df_i$`Assigned Surveys`, na.rm = TRUE)),
            `AM Assigned` = as.integer(am),
            `PM Assigned` = as.integer(pm),
            check.names = FALSE, stringsAsFactors = FALSE
          )
        }
      })
      total_row <- data.frame(
        Day = "Total",
        `Assigned Total` = as.integer(total_assigned),
        `AM Assigned` = as.integer((bins$wd_am %||% 0L) + (bins$we_am %||% 0L)),
        `PM Assigned` = as.integer((bins$wd_pm %||% 0L) + (bins$we_pm %||% 0L)),
        check.names = FALSE, stringsAsFactors = FALSE
      )
      summary_tbl <- do.call(rbind, c(list(total_row), per_slot_rows))
      openxlsx::writeData(wb, "Summary & Diagnostics", to_excel_df(summary_tbl), startRow = r, keepNA = FALSE)
      openxlsx::setColWidths(wb, sheet = "Summary & Diagnostics",
                             cols = 2:safe_ncol(summary_tbl),
                             widths = "auto")
      # NOTE: intentionally NO freezePane here for the first sheet
      
      # ---------- Remaining sheets (with freeze on first row) ----------
      if (is.null(days) || length(days) == 0) {
        openxlsx::addWorksheet(wb, "No Schedule")
        openxlsx::writeData(wb, "No Schedule", data.frame(Message = "No schedule yet. Click Generate in the app."), keepNA = FALSE)
        openxlsx::freezePane(wb, "No Schedule", firstRow = TRUE)
      } else {
        for (i in seq_along(days)) {
          sheet_name <- paste0("Day ", i, " (", days[i], ")")
          if (nchar(sheet_name) > 31) sheet_name <- substr(sheet_name, 1, 31)
          openxlsx::addWorksheet(wb, sheet_name)
          df <- if (i >= 1L && i <= length(state$schedules)) state$schedules[[i]] else NULL
          if (is.null(df) || !is.data.frame(df) || nrow(df) == 0) {
            openxlsx::writeData(wb, sheet = sheet_name, x = data.frame(Message = "No assignments for this day"), keepNA = FALSE)
          } else {
            # Enforce AM/PM time using DepMin before dropping it
            if ("DepMin" %in% names(df)) {
              df$`Departure Time` <- vapply(df$DepMin, mins_to_ampm, character(1))
            }
            # Sort by actual departure minutes so the sheet matches in-app ordering
            if ("DepMin" %in% names(df)) {
              df <- df[order(df$DepMin), , drop = FALSE]
            }
            df_exp <- df %>% dplyr::select(-dplyr::any_of(c("DepMin", "Unique Route Number")))
            df_exp <- to_excel_df(df_exp)
            # Enforce export column order to match the app
            keep_order <- c(
              "Day", "Airline", "Destination", "Departure Time", "Assigned Surveys",
              "Flight #", "Concourse", "Flight Type", "Gate", "Airline Code", "Destination Code"
            )
            keep <- intersect(keep_order, names(df_exp))
            df_exp <- dplyr::select(df_exp, dplyr::all_of(keep))
            day_label <- (state$day_list %||% character(0))[i]
            if (is.null(day_label) || is.na(day_label) || !nzchar(day_label)) day_label <- ""
            if ("Assigned Surveys" %in% names(df_exp)) df_exp[["Assigned Surveys"]] <- as.integer(df_exp[["Assigned Surveys"]])
            openxlsx::writeData(wb, sheet = sheet_name, x = df_exp, keepNA = FALSE)
          }
          openxlsx::freezePane(wb, sheet = sheet_name, firstRow = TRUE)
          openxlsx::setColWidths(wb, sheet = sheet_name, cols = 1:safe_ncol(df_exp), widths = "auto")
        }
      }
      
      uru <- state$routes_updated
      if (is.null(uru) || !is.data.frame(uru)) uru <- data.frame(Message = "None")
      uru <- to_excel_df(uru); if (ncol(uru) == 0) uru <- data.frame(Message = "None")
      if ("Assigned Surveys" %in% names(uru)) uru[["Assigned Surveys"]] <- as.integer(uru[["Assigned Surveys"]])
      openxlsx::addWorksheet(wb, "Updated Routes Remaining")
      openxlsx::writeData(wb, sheet = "Updated Routes Remaining", x = uru, keepNA = FALSE)
      openxlsx::freezePane(wb, sheet = "Updated Routes Remaining", firstRow = TRUE)
      openxlsx::setColWidths(wb, sheet = "Updated Routes Remaining", cols = 1:safe_ncol(uru), widths = "auto")
      
      openxlsx::addWorksheet(wb, "Surveys Completed")
      sc <- state$assigned_long
      if (is.null(sc) || !is.data.frame(sc) || nrow(sc) == 0) {
        sc <- data.frame(Message = "No surveys were scheduled")
      } else {
        # Keep DepMin for reliable AM/PM conversion, then drop it before writing
        keep <- c("Day","Airline","Concourse","Destination","Flight #","Departure Time","Assigned Surveys","Flight Type","Airline Code","Destination Code","Unique Route Number","DepMin")
        keep <- intersect(keep, names(sc))
        sc <- dplyr::select(sc, dplyr::all_of(keep))
        
        if ("DepMin" %in% names(sc)) {
          sc[["Departure Time"]] <- vapply(as.integer(sc$DepMin), mins_to_ampm, character(1))
          sc$DepMin <- NULL
        } else {
          tt_min <- vapply(as.character(sc[["Departure Time"]]), parse_user_time, integer(1))
          sc[["Departure Time"]] <- vapply(tt_min, mins_to_ampm, character(1))
        }
      }
      sc <- to_excel_df(sc)
      if ("Assigned Surveys" %in% names(sc)) sc[["Assigned Surveys"]] <- as.integer(sc[["Assigned Surveys"]])
      openxlsx::writeData(wb, sheet = "Surveys Completed", x = sc, keepNA = FALSE)
      openxlsx::freezePane(wb, sheet = "Surveys Completed", firstRow = TRUE)
      openxlsx::setColWidths(wb, sheet = "Surveys Completed", cols = 1:safe_ncol(sc), widths = "auto")
      openxlsx::addWorksheet(wb, "Date Fit Summary")
      fit <- state$date_fit
      if (is.null(fit) || !nrow(fit)) fit <- data.frame(Message = "No schedules yet.")
      fit <- to_excel_df(fit)
      openxlsx::writeData(wb, sheet = "Date Fit Summary", x = fit, keepNA = FALSE)
      
      openxlsx::addWorksheet(wb, "Required Routes with No Flights")
      ru <- state$nf_tbl
      if (is.null(ru)) ru <- data.frame(Message = "None")
      ru <- to_excel_df(ru); if (ncol(ru) == 0) ru <- data.frame(Message = "None")
      if ("Assigned Surveys" %in% names(ru)) ru[["Assigned Surveys"]] <- as.integer(ru[["Assigned Surveys"]])
      openxlsx::writeData(wb, sheet = "Required Routes with No Flights", x = ru, keepNA = FALSE)
      openxlsx::freezePane(wb, sheet = "Required Routes with No Flights", firstRow = TRUE)
      openxlsx::setColWidths(wb, sheet = "Required Routes with No Flights", cols = 1:safe_ncol(ru), widths = "auto")
      openxlsx::freezePane(wb, sheet = "Date Fit Summary", firstRow = TRUE)
      openxlsx::setColWidths(wb, sheet = "Date Fit Summary", cols = 1:safe_ncol(fit), widths = "auto")
      
      # ---- Debug Trace (for troubleshooting) ----
      openxlsx::addWorksheet(wb, "Debug Trace")
      
      # Build the same flattened table that the app shows in the Debug Trace tab
      rows <- state$debug %||% list()
      if (!length(rows)) {
        dbg <- data.frame(Message = "No debug entries captured in this run", stringsAsFactors = FALSE)
      } else {
        keys <- unique(unlist(lapply(rows, names)))
        if (is.null(keys) || !length(keys)) keys <- c("Day","Slot","Step")
        mat <- lapply(rows, function(x) {
          out <- setNames(as.list(rep(NA_character_, length(keys))), keys)
          for (nm in names(x)) out[[nm]] <- as.character(x[[nm]])
          out
        })
        dbg <- as_plain_df(dplyr::bind_rows(mat))
      }
      
      # Keep first columns human-legible and stable
      dbg <- to_excel_df(dbg)
      openxlsx::writeData(wb, sheet = "Debug Trace", x = dbg, keepNA = FALSE)
      openxlsx::freezePane(wb, sheet = "Debug Trace", firstRow = TRUE)
      openxlsx::setColWidths(wb, sheet = "Debug Trace", cols = 1:safe_ncol(dbg), widths = "auto")
      tmp <- tempfile(fileext = ".xlsx")
      openxlsx::saveWorkbook(wb, tmp, overwrite = TRUE)
      file.copy(tmp, file, overwrite = TRUE)
    }
  )
  outputOptions(output, "download", suspendWhenHidden = FALSE)
}
options(shiny.sanitize.errors = FALSE)
options(shiny.fullstacktrace = FALSE)
shinyApp(ui, server)

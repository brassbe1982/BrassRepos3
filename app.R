# ==============================================================================
# Complete Shiny App: Advanced Economics of Strategy – Strategy Analytics Platform
# DBA Course 0501750, Al Ain University, Semester S2 2025-2026
# Instructor: Prof. Ibrahim Niankara
# Updated: January 2026
# Version: 4.0 (Enhanced with Copula Modeling)
# 
# NEW FEATURES (v4.0):
# - Data Quality Dashboard with diagnostics
# - Analysis Activity Log with session tracking
# - Progress indicators for long operations
# - Enhanced error handling and validation
# - Caching for improved performance
# - CSV file support
# - Tooltips and improved UX
# - Session statistics and cache management
# - INTEGRATED COPULA MODELING (GJRM) for advanced dependence modeling
# ==============================================================================

# ==============================================================================
# CONFIGURATION SETTINGS
# ==============================================================================
APP_CONFIG <- list(
  title = "Advanced Economics of Strategy – Analytics Platform",
  version = "4.0",
  course = "0501750 Advanced Economics of Strategy",
  semester = "S2 2025-2026",
  instructor = "Prof. Ibrahim Niankara",
  institution = "College of Business, Al Ain University"
)

UPLOAD_CONFIG <- list(
  max_size_mb = 100,
  allowed_extensions = c("dta", "rda", "RData", "csv"),
  timeout_seconds = 300
)

CACHE_CONFIG <- list(
  enabled = TRUE,
  directory = "cache",
  max_age_hours = 24,
  auto_clean = TRUE
)

ANALYSIS_CONFIG <- list(
  min_observations = 30,
  bootstrap_iterations = 1000,
  confidence_level = 0.95
)

VIZ_CONFIG <- list(
  default_colors = c("#2ecc71", "#3498db", "#e74c3c", "#f39c12", "#9b59b6"),
  map_colors = "YlOrRd"
)

# ==============================================================================
# LOAD REQUIRED PACKAGES
# ==============================================================================
library(shiny)
library(shinydashboard)
library(shinyWidgets)
library(shinyjs)       # For enhanced UI interactions
library(shinyBS)       # For tooltips
library(DT)
library(dplyr)
library(haven)
library(stringr)
library(purrr)
library(Hmisc)
library(tmap)
library(sf)
library(plotly)
library(ggplot2)
library(tidyr)
library(visNetwork)
library(broom)
library(FactoMineR)
library(entropy)
library(grf)
library(cobalt)
library(survey)
library(rlang)
library(countrycode)
library(digest)
library(gridExtra)
library(GJRM)          # NEW: For copula modeling
library(mgcv)          # NEW: For GAM diagnostics
library(shinydashboardPlus)  # NEW: For enhanced UI
library(viridis)
library(RColorBrewer)

# Set options
options(
  shiny.maxRequestSize = UPLOAD_CONFIG$max_size_mb * 1024^2,
  shiny.sanitize.errors = FALSE
)

# ==============================================================================
# UTILITY FUNCTIONS
# ==============================================================================

# Validate file upload
validate_upload <- function(file_input) {
  req(file_input)
  ext <- tools::file_ext(file_input$name)
  
  if(!ext %in% UPLOAD_CONFIG$allowed_extensions) {
    stop(paste("Please upload a valid file. Supported formats:", 
               paste(UPLOAD_CONFIG$allowed_extensions, collapse = ", ")))
  }
  
  if(file.size(file_input$datapath) > UPLOAD_CONFIG$max_size_mb * 1024^2) {
    stop(paste("File size must be less than", UPLOAD_CONFIG$max_size_mb, "MB"))
  }
  
  return(TRUE)
}

# Load data safely
load_data_safe <- function(filepath) {
  ext <- tools::file_ext(filepath)
  
  data <- tryCatch({
    if(ext == "dta") {
      haven::read_dta(filepath)
    } else if(ext %in% c("rda", "RData")) {
      env <- new.env()
      load(filepath, envir = env)
      objs <- ls(envir = env)
      df_objs <- objs[sapply(objs, function(x) is.data.frame(get(x, envir = env)))]
      if(length(df_objs) == 0) stop("No data frame found in .rda/.RData file")
      get(df_objs[1], envir = env)
    } else if(ext == "csv") {
      read.csv(filepath, stringsAsFactors = FALSE)
    } else {
      stop("Unsupported file format")
    }
  }, error = function(e) {
    stop(paste("Error loading data:", e$message))
  })
  
  if(!is.data.frame(data)) {
    stop("Loaded object is not a data frame")
  }
  
  if(nrow(data) == 0) {
    stop("Data frame is empty")
  }
  
  return(data)
}

# Calculate data quality metrics
calculate_data_quality <- function(data) {
  if(is.null(data) || nrow(data) == 0) {
    return(NULL)
  }
  
  quality_metrics <- list(
    total_rows = nrow(data),
    total_cols = ncol(data),
    missing_pct = round(mean(is.na(data)) * 100, 2),
    complete_rows = sum(complete.cases(data)),
    numeric_vars = sum(sapply(data, is.numeric)),
    factor_vars = sum(sapply(data, is.factor)),
    char_vars = sum(sapply(data, is.character))
  )
  
  var_quality <- data.frame(
    Variable = names(data),
    Type = sapply(data, function(x) class(x)[1]),
    Missing = colSums(is.na(data)),
    Missing_Pct = round(colSums(is.na(data)) / nrow(data) * 100, 2),
    Unique = sapply(data, function(x) length(unique(na.omit(x)))),
    stringsAsFactors = FALSE
  )
  
  list(
    summary = quality_metrics,
    variables = var_quality
  )
}

# Create analysis log entry
create_log_entry <- function(action, details = "", status = "success") {
  data.frame(
    timestamp = format(Sys.time(), "%Y-%m-%d %H:%M:%S"),
    action = action,
    details = details,
    status = status,
    stringsAsFactors = FALSE
  )
}

# Sanitize custom mutate expressions
sanitize_mutate <- function(expr) {
  if(is.null(expr) || nchar(trimws(expr)) == 0) {
    return(NULL)
  }
  
  dangerous_patterns <- c(
    "system\\(", "eval\\(", "source\\(", "file\\.remove",
    "unlink\\(", "download\\.file", "install\\.packages",
    "library\\(", "require\\(", "rm\\(", "<<-"
  )
  
  for(pattern in dangerous_patterns) {
    if(grepl(pattern, expr, ignore.case = TRUE)) {
      stop(paste("Expression contains forbidden pattern:", pattern))
    }
  }
  
  exprs <- strsplit(expr, "\n")[[1]]
  exprs <- trimws(exprs)
  exprs <- exprs[nchar(exprs) > 0]
  
  return(exprs)
}

# Clean temporary files
clean_temp_files <- function(cache_dir = "cache", max_age_hours = 24) {
  if(!dir.exists(cache_dir)) return(invisible(NULL))
  
  files <- list.files(cache_dir, full.names = TRUE)
  for(file in files) {
    file_age <- difftime(Sys.time(), file.info(file)$mtime, units = "hours")
    if(file_age > max_age_hours) {
      unlink(file)
    }
  }
}

# Bootstrap confidence intervals
bootstrap_ci <- function(data, statistic_fn, n_boot = 1000, conf_level = 0.95) {
  boot_stats <- replicate(n_boot, {
    boot_sample <- data[sample(nrow(data), replace = TRUE), ]
    statistic_fn(boot_sample)
  })
  
  alpha <- 1 - conf_level
  ci <- quantile(boot_stats, probs = c(alpha/2, 1 - alpha/2), na.rm = TRUE)
  
  list(
    estimate = mean(boot_stats, na.rm = TRUE),
    lower = ci[1],
    upper = ci[2],
    boot_estimates = boot_stats
  )
}

# ==============================================================================
# UI Definition
# ==============================================================================
ui <- dashboardPage(
  skin = "green",
  
  dashboardHeader(
    title = span(
      tags$img(src = "https://www.aau.ac.ae/images/logo.png", height = "40px", 
               style = "margin-right:10px;"),
      paste(APP_CONFIG$title, "v", APP_CONFIG$version)
    ),
    titleWidth = 600
  ),
  
  dashboardSidebar(
    width = 300,
    sidebarMenu(
      id = "sidebar",
      menuItem("Home & Overview", tabName = "home", icon = icon("home")),
      menuItem("1. Data Preprocessing", tabName = "preprocess", icon = icon("cogs")),
      menuItem("2. Data Quality", tabName = "quality", icon = icon("check-circle")),
      menuItem("3. Spatial Mapping", tabName = "mapping", icon = icon("globe")),
      menuItem("4. Strategy Evaluation", tabName = "strategy", icon = icon("chart-bar")),
      menuItem("5. Causal Inference (ML)", tabName = "causal", icon = icon("balance-scale")),
      menuItem("6. Copula Modeling (GJRM)", tabName = "copula", icon = icon("link")),
      menuItem("Results & Export", tabName = "export", icon = icon("download")),
      menuItem("Analysis Log", tabName = "log", icon = icon("history"))
    ),
    
    hr(),
    
    tags$div(style = "padding: 10px;",
             tags$h4("Data Controls", style = "color:#fff;"),
             fileInput("data_upload", "Upload Dataset (.dta / .rda / .csv)",
                       accept = c(".dta", ".rda", ".RData", ".csv")),
             actionButton("load_sample", "Load Sample Data", 
                          class = "btn-info btn-block", icon = icon("database")),
             hr(),
             tags$p(tags$strong("Course:"), APP_CONFIG$course),
             tags$p(tags$strong("Semester:"), APP_CONFIG$semester),
             tags$p(tags$strong("Instructor:"), APP_CONFIG$instructor),
             tags$p(tags$small(APP_CONFIG$institution))
    )
  ),
  
  dashboardBody(
    # Add shinyjs and custom CSS
    useShinyjs(),
    
    tags$head(
      tags$style(HTML("
        .info-box { cursor: pointer; }
        .small-box { cursor: pointer; }
        .bg-aqua { background-color: #00c0ef !important; }
        .bg-green { background-color: #00a65a !important; }
        .bg-yellow { background-color: #f39c12 !important; }
        .bg-purple { background-color: #605ca8 !important; }
        .progress { margin-bottom: 5px; }
        .shiny-notification { position: fixed; top: 50px; right: 10px; }
        .quality-good { color: #27ae60; }
        .quality-warning { color: #f39c12; }
        .quality-bad { color: #e74c3c; }
        .formula-preview { 
          font-family: monospace; 
          background-color: #f0f0f0; 
          padding: 10px; 
          border: 1px solid #ccc; 
          border-radius: 4px;
          white-space: pre-wrap;
          margin-top: 10px;
        }
        .box-header h3 { color: #2c3e50; }
        .btn-purple { background-color: #605ca8; color: white; }
        .btn-purple:hover { background-color: #4a4786; color: white; }
      "))
    ),
    
    tabItems(
      # ----------------------------------------------------------------------
      # Home Tab
      # ----------------------------------------------------------------------
      tabItem(tabName = "home",
              fluidRow(
                box(width = 12, title = "Welcome to Strategy Analytics Platform v4.0", 
                    status = "success", solidHeader = TRUE,
                    tags$h3(APP_CONFIG$course),
                    tags$p("This enhanced platform implements the full empirical research pipeline 
                           using World Bank Enterprise Surveys (WBES) data, with advanced features:"),
                    tags$ul(
                      tags$li(tags$strong("Smart Data Preprocessing:"), 
                              "Intelligent filtering, validation, and transformation with quality checks"),
                      tags$li(tags$strong("Data Quality Dashboard:"), 
                              "Real-time diagnostics and missing data analysis"),
                      tags$li(tags$strong("Interactive Spatial Mapping:"), 
                              "Country-level aggregation with weighted statistics"),
                      tags$li(tags$strong("Comprehensive Strategy Evaluation:"), 
                              "Full framework including diagnostics, tests, dominance analysis, and network visualization"),
                      tags$li(tags$strong("Advanced Causal Inference:"), 
                              "ML-based Causal Forest, IPW, Doubly Robust estimation with diagnostics"),
                      tags$li(tags$strong("Copula Modeling (NEW):"), 
                              "GJRM framework for bivariate/trivariate dependence modeling, selection models, and survival analysis"),
                      tags$li(tags$strong("Performance Optimizations:"), 
                              "Progress tracking and efficient computation"),
                      tags$li(tags$strong("Analysis Activity Log:"), 
                              "Track all operations with session statistics")
                    ),
                    tags$hr(),
                    tags$h4("Quick Start Guide:"),
                    tags$ol(
                      tags$li("Upload your WBES dataset or load sample data"),
                      tags$li("Review data quality metrics in the Data Quality tab"),
                      tags$li("Preprocess: select variables, filter, and transform"),
                      tags$li("Perform spatial mapping and strategy evaluation"),
                      tags$li("Run causal inference analysis"),
                      tags$li("Use copula modeling for dependence structures"),
                      tags$li("Export results and reports")
                    )
                )
              ),
              
              fluidRow(
                valueBoxOutput("total_firms", width = 4),
                valueBoxOutput("total_countries", width = 4),
                valueBoxOutput("data_quality_score", width = 4)
              ),
              
              fluidRow(
                infoBoxOutput("last_action", width = 4),
                infoBoxOutput("cache_status", width = 4),
                infoBoxOutput("analysis_count", width = 4)
              )
      ),
      
      # ----------------------------------------------------------------------
      # Data Quality Tab
      # ----------------------------------------------------------------------
      tabItem(tabName = "quality",
              fluidRow(
                box(width = 12, title = "Data Quality Dashboard", 
                    status = "primary", solidHeader = TRUE,
                    tags$p("Comprehensive data quality metrics and diagnostics for your dataset")
                )
              ),
              
              fluidRow(
                valueBoxOutput("quality_completeness", width = 3),
                valueBoxOutput("quality_missing", width = 3),
                valueBoxOutput("quality_numeric", width = 3),
                valueBoxOutput("quality_categorical", width = 3)
              ),
              
              fluidRow(
                box(width = 6, title = "Missing Data Analysis", status = "warning",
                    plotlyOutput("quality_missing_plot", height = "400px")
                ),
                box(width = 6, title = "Variable Type Distribution", status = "info",
                    plotlyOutput("vartype_plot", height = "400px")
                )
              ),
              
              fluidRow(
                box(width = 12, title = "Variable-Level Quality Metrics", status = "primary",
                    DTOutput("quality_table")
                )
              ),
              
              fluidRow(
                box(width = 12, title = "Data Quality Recommendations", status = "success",
                    uiOutput("quality_recommendations")
                )
              )
      ),
      
      # ----------------------------------------------------------------------
      # Preprocessing Tab
      # ----------------------------------------------------------------------
      tabItem(tabName = "preprocess",
              fluidRow(
                box(width = 4, title = "Data Summary", status = "info", solidHeader = TRUE,
                    verbatimTextOutput("data_summary"),
                    tags$hr(),
                    tags$p(tags$strong("Current data:"), textOutput("data_dimensions", inline = TRUE)),
                    tags$p(tags$strong("Quality Score:"), textOutput("quality_score_text", inline = TRUE))
                ),
                
                box(width = 8, title = "Variable Selection & Filtering", status = "primary", solidHeader = TRUE,
                    fluidRow(
                      column(6,
                             pickerInput("keep_vars", "Variables to Keep",
                                         choices = NULL, multiple = TRUE, 
                                         options = list(`actions-box` = TRUE, `live-search` = TRUE,
                                                        `selected-text-format` = "count > 3"))
                      ),
                      column(6,
                             pickerInput("nonneg_vars", "Non-negative Variables (>=0 filter)",
                                         choices = NULL, multiple = TRUE,
                                         options = list(`actions-box` = TRUE))
                      )
                    ),
                    fluidRow(
                      column(6,
                             numericInput("min_obs", "Minimum observations per group:", 
                                          value = 30, min = 1, max = 1000)
                      ),
                      column(6,
                             checkboxInput("remove_missing", "Remove rows with missing values", FALSE)
                      )
                    ),
                    actionButton("apply_filter", "Apply Filtering", 
                                 class = "btn-success btn-block", icon = icon("filter"))
                )
              ),
              
              fluidRow(
                box(width = 6, title = "Recoding & Custom Mutations", status = "primary", solidHeader = TRUE,
                    checkboxGroupInput("recodes", "Standard Recodes",
                                       choices = c("Fix missing trade_pos" = "trade_pos",
                                                   "Fix survey dates" = "dates",
                                                   "Binary foreign ownership (a7)" = "foreign",
                                                   "Create country codes" = "country_code",
                                                   "Standardize weights" = "weights"),
                                       selected = c("trade_pos", "dates", "foreign", "country_code", "weights")),
                    
                    textAreaInput("custom_mutate", "Custom mutate expressions (one per line)",
                                  placeholder = "e.g.\nage = a14y - b5\nsize_log = log(nFulTimEmplyLFY + 1)\nprofit_margin = (rev - cost)/rev", 
                                  rows = 6),
                    
                    actionButton("apply_recodes", "Apply Recodes & Mutations", 
                                 class = "btn-success btn-block", icon = icon("edit"))
                ),
                
                box(width = 6, title = "Variable Transformation", status = "primary", solidHeader = TRUE,
                    pickerInput("transform_vars", "Variables to Transform",
                                choices = NULL, multiple = TRUE,
                                options = list(`actions-box` = TRUE)),
                    selectInput("transform_type", "Transformation Type",
                                choices = c("Logarithmic (log(x+1))" = "log",
                                            "Standardize (z-score)" = "zscore",
                                            "Normalize (0-1)" = "normalize",
                                            "Square root" = "sqrt",
                                            "Inverse hyperbolic sine" = "asinh")),
                    actionButton("apply_transform", "Apply Transformation",
                                 class = "btn-warning btn-block", icon = icon("calculator"))
                )
              ),
              
              fluidRow(
                tabBox(width = 12, title = "Processed Data",
                       tabPanel("Data Preview", DTOutput("processed_table")),
                       tabPanel("Missing Values", plotlyOutput("missing_plot"), DTOutput("missing_table")),
                       tabPanel("Variable Summary", DTOutput("var_summary")),
                       tabPanel("Distribution Plots", plotlyOutput("dist_plots")),
                       tabPanel("Correlation Matrix", plotlyOutput("correlation_matrix"))
                )
              )
      ),
      
      # ----------------------------------------------------------------------
      # Spatial Mapping Tab
      # ----------------------------------------------------------------------
      tabItem(tabName = "mapping",
              fluidRow(
                box(width = 3, title = "Mapping Settings", status = "warning", solidHeader = TRUE,
                    selectInput("map_type", "Map Type",
                                choices = c("Interactive (tmap)" = "interactive",
                                            "Static (ggplot)" = "static",
                                            "Choropleth" = "choropleth")),
                    
                    pickerInput("binary_map_vars", "Binary Variables (% adoption)",
                                choices = NULL, multiple = TRUE,
                                options = list(`actions-box` = TRUE, `max-options` = 5)),
                    
                    pickerInput("cont_map_vars", "Continuous Variables (Mean + SD)",
                                choices = NULL, multiple = TRUE,
                                options = list(`actions-box` = TRUE, `max-options` = 5)),
                    
                    selectInput("weight_var", "Weight Variable",
                                choices = c("wstrict", "None" = "none")),
                    
                    selectInput("color_palette", "Color Palette",
                                choices = c("Viridis" = "viridis",
                                            "Blues" = "Blues",
                                            "Reds" = "Reds",
                                            "Greens" = "Greens",
                                            "Spectral" = "Spectral")),
                    
                    actionButton("run_aggregation", "Generate Map", 
                                 class = "btn-warning btn-block", icon = icon("map"))
                ),
                
                box(width = 9, title = "Interactive Map", status = "warning",
                    conditionalPanel(
                      condition = "input.map_type == 'interactive'",
                      tmapOutput("tmap_plot", height = "600px")
                    ),
                    conditionalPanel(
                      condition = "input.map_type == 'static'",
                      plotlyOutput("static_map", height = "600px")
                    ),
                    conditionalPanel(
                      condition = "input.map_type == 'choropleth'",
                      plotlyOutput("choropleth_map", height = "600px")
                    )
                )
              ),
              
              fluidRow(
                tabBox(width = 12, title = "Aggregated Data",
                       tabPanel("Country-Level Data", DTOutput("agg_table")),
                       tabPanel("Regional Summary", DTOutput("region_table")),
                       tabPanel("Map Data Download", 
                                downloadButton("download_map_data", "Download Map Data (.csv)"),
                                tags$hr(),
                                DTOutput("map_data_preview"))
                )
              )
      ),
      
      # ----------------------------------------------------------------------
      # Strategy Effectiveness Tab
      # ----------------------------------------------------------------------
      tabItem(tabName = "strategy",
              fluidRow(
                box(width = 3, title = "Strategy Selection", status = "danger", solidHeader = TRUE,
                    selectInput("strategy_var", "Strategy Index to Evaluate",
                                choices = c("ISVI", "FIVI", "EMSI", "UMSI", 
                                            "CO2MSI", "GSVI", "SGPII", "EVMSSI"),
                                selected = "ISVI"),
                    
                    pickerInput("outcome_metrics", "Performance Outcomes",
                                choices = NULL, multiple = TRUE,
                                options = list(`actions-box` = TRUE, `max-options` = 10)),
                    
                    checkboxInput("use_weights", "Use Survey Weights", TRUE),
                    
                    sliderInput("confidence_level", "Confidence Level (%)",
                                min = 80, max = 99, value = 95, step = 1)
                ),
                
                box(width = 3, title = "Analysis Options", status = "danger",
                    checkboxGroupInput("analyses", "Analyses to Perform",
                                       choices = c("Frequency Distribution" = "freq",
                                                   "Descriptive Statistics" = "desc",
                                                   "Volatility Analysis" = "volatility",
                                                   "Statistical Tests" = "tests",
                                                   "Pairwise Dominance" = "dominance",
                                                   "Dominance Network" = "network",
                                                   "Pareto Frontier" = "pareto",
                                                   "Entropy Index" = "entropy",
                                                   "PCA Analysis" = "pca",
                                                   "Cluster Analysis" = "cluster"),
                                       selected = c("freq", "desc", "volatility", "tests", 
                                                    "dominance", "pareto", "entropy", "pca"))
                ),
                
                box(width = 6, title = "Advanced Settings", status = "danger",
                    fluidRow(
                      column(6,
                             numericInput("n_bootstrap", "Bootstrap iterations", 
                                          value = 100, min = 10, max = 1000),
                             numericInput("pca_components", "PCA components", 
                                          value = 3, min = 1, max = 10),
                             selectInput("distance_metric", "Distance metric for clustering",
                                         choices = c("Euclidean" = "euclidean",
                                                     "Manhattan" = "manhattan",
                                                     "Correlation" = "correlation"))
                      ),
                      column(6,
                             selectInput("clustering_method", "Clustering method",
                                         choices = c("k-means" = "kmeans",
                                                     "Hierarchical" = "hclust",
                                                     "DBSCAN" = "dbscan")),
                             numericInput("n_clusters", "Number of clusters",
                                          value = 3, min = 2, max = 10),
                             checkboxInput("normalize_before_pca", "Normalize before PCA", TRUE)
                      )
                    ),
                    actionButton("run_strategy_analysis", "Run Full Evaluation", 
                                 class = "btn-danger btn-block", icon = icon("play"))
                )
              ),
              
              fluidRow(
                tabBox(width = 12, title = "Strategy Effectiveness Results",
                       tabPanel("Summary Dashboard",
                                fluidRow(
                                  valueBoxOutput("total_strategies"),
                                  valueBoxOutput("pareto_count"),
                                  valueBoxOutput("best_strategy")
                                ),
                                plotlyOutput("summary_radar")
                       ),
                       tabPanel("Frequency", 
                                fluidRow(
                                  column(6, DTOutput("freq_table")),
                                  column(6, plotlyOutput("freq_bar"))
                                )),
                       tabPanel("Descriptive Statistics", 
                                DTOutput("desc_table"),
                                plotlyOutput("desc_boxplot")),
                       tabPanel("Volatility Analysis", 
                                plotlyOutput("volatility_plot"),
                                DTOutput("volatility_table")),
                       tabPanel("Statistical Tests", 
                                verbatimTextOutput("stat_tests"),
                                plotlyOutput("test_plots")),
                       tabPanel("Dominance Analysis",
                                fluidRow(
                                  column(6, plotlyOutput("dominance_heatmap")),
                                  column(6, DTOutput("dominance_matrix"))
                                ),
                                visNetworkOutput("dominance_network")),
                       tabPanel("Pareto Frontier",
                                fluidRow(
                                  column(6, DTOutput("pareto_table")),
                                  column(6, plotlyOutput("pareto_plot"))
                                ),
                                plotlyOutput("pareto_radar")),
                       tabPanel("Composite Indices",
                                fluidRow(
                                  column(6, DTOutput("composite_table")),
                                  column(6, plotlyOutput("composite_plot"))
                                ),
                                plotlyOutput("composite_radar")),
                       tabPanel("Cluster Analysis",
                                plotlyOutput("cluster_plot"),
                                DTOutput("cluster_table"))
                )
              )
      ),
      
      # ----------------------------------------------------------------------
      # Causal Inference Tab
      # ----------------------------------------------------------------------
      tabItem(tabName = "causal",
              fluidRow(
                box(width = 12, title = "Causal Inference Analysis – Settings", status = "primary", solidHeader = TRUE,
                    infoBox(width = 12, title = "Purpose", 
                            "Estimate causal effects of strategies on outcomes, moving beyond correlation to identification. 
                            Supports classic econometric methods and modern ML (Causal Forest).", 
                            icon = icon("info-circle"), color = "purple"),
                    fluidRow(
                      column(3,
                             selectInput("treatment_var", "Binary Treatment Variable (1 = treated, 0 = control)",
                                         choices = NULL),
                             tags$small("Create binary indicators in preprocessing if needed")
                      ),
                      column(3,
                             selectInput("causal_outcome", "Outcome Variable (continuous preferred)",
                                         choices = NULL)
                      ),
                      column(3,
                             selectInput("causal_method", "Causal Estimation Method",
                                         choices = c(
                                           "Regression Adjustment" = "reg",
                                           "Inverse Probability Weighting (IPW)" = "ipw",
                                           "Doubly Robust (DR)" = "dr",
                                           "Causal Forest (ML)" = "cf"
                                         ))
                      ),
                      column(3,
                             numericInput("cf_trees", "Causal Forest trees (if selected)",
                                          value = 2000, min = 100, max = 10000),
                             checkboxInput("cf_honesty", "Use honesty in Causal Forest", TRUE)
                      )
                    ),
                    pickerInput("causal_covars", "Covariates for Adjustment/Balancing",
                                choices = NULL, multiple = TRUE,
                                options = list(`actions-box` = TRUE, `live-search` = TRUE)),
                    actionButton("run_causal", "Run Causal Analysis", 
                                 class = "btn-primary btn-block", icon = icon("calculator"))
                )
              ),
              
              fluidRow(
                tabBox(width = 12, title = "Causal Inference Results",
                       tabPanel("Method Summary", 
                                verbatimTextOutput("causal_summary"),
                                tags$hr(),
                                plotlyOutput("causal_effect_plot")),
                       tabPanel("Balance Diagnostics", 
                                plotOutput("balance_plot"),
                                DTOutput("balance_table")),
                       tabPanel("Average Treatment Effect", 
                                DTOutput("ate_table"),
                                plotlyOutput("ate_forest_plot")),
                       tabPanel("Heterogeneity (CATE)", 
                                plotlyOutput("cate_plot"),
                                DTOutput("cate_table")),
                       tabPanel("Sensitivity Analysis",
                                plotlyOutput("sensitivity_plot"),
                                verbatimTextOutput("sensitivity_summary"))
                )
              )
      ),
      
      # ----------------------------------------------------------------------
      # Copula Modeling Tab (NEW)
      # ----------------------------------------------------------------------
      tabItem(tabName = "copula",
              fluidRow(
                box(width = 12, title = "Copula Modeling with GJRM", status = "purple", solidHeader = TRUE,
                    infoBox(width = 12, title = "Purpose",
                            "Model complex dependence structures, selection models, and survival analysis using copulas.
                            Supports bivariate/trivariate models with various marginal distributions and copula families.",
                            icon = icon("link"), color = "purple")
                )
              ),
              
              fluidRow(
                box(title = "Model Type & Equations", status = "primary", solidHeader = TRUE, width = 12,
                    selectInput("copula_model", "Model Type",
                                choices = c(
                                  "Bivariate" = "B",
                                  "Trivariate" = "T",
                                  "Bivariate Sample Selection" = "BSS",
                                  "Trivariate Double Selection" = "TSS",
                                  "Trivariate Endogeneity & Selection" = "TESS",
                                  "Bivariate Partial Observability" = "BPO",
                                  "Bivariate Partial Observability (zero corr)" = "BPO0",
                                  "Roy Switching Regression" = "ROY"
                                ))
                )
              ),
              
              fluidRow(
                box(title = "Important Ordering Notes", status = "warning", solidHeader = TRUE, width = 12,
                    tags$ul(
                      tags$li("For selection models (BSS/TSS/TESS), first equation(s) are selection."),
                      tags$li("Binary before continuous/discrete when mixed."),
                      tags$li("Discrete before continuous when mixed.")
                    )
                )
              ),
              
              fluidRow(
                column(4,
                       box(title = "Equation 1", status = "primary", solidHeader = TRUE, width = NULL,
                           selectInput("resp1", "Response Variable 1", choices = NULL),
                           selectizeInput("preds1_lin", "Linear Predictors", choices = NULL, multiple = TRUE),
                           selectizeInput("preds1_sm", "Smooth Predictors – s()", choices = NULL, multiple = TRUE)
                       )
                ),
                column(4,
                       box(title = "Equation 2", status = "primary", solidHeader = TRUE, width = NULL,
                           selectInput("resp2", "Response Variable 2", choices = NULL),
                           selectizeInput("preds2_lin", "Linear Predictors", choices = NULL, multiple = TRUE),
                           selectizeInput("preds2_sm", "Smooth Predictors – s()", choices = NULL, multiple = TRUE)
                       )
                ),
                column(4,
                       conditionalPanel(
                         condition = "input.copula_model == 'T' || input.copula_model == 'TSS' || input.copula_model == 'TESS'",
                         box(title = "Equation 3", status = "primary", solidHeader = TRUE, width = NULL,
                             selectInput("resp3", "Response Variable 3", choices = NULL),
                             selectizeInput("preds3_lin", "Linear Predictors", choices = NULL, multiple = TRUE),
                             selectizeInput("preds3_sm", "Smooth Predictors – s()", choices = NULL, multiple = TRUE)
                         )
                       )
                )
              ),
              
              fluidRow(
                box(title = "Advanced Formula Mode", status = "info", solidHeader = TRUE, width = 12,
                    checkboxInput("advanced_formula", "Use advanced manual formula entry (for complex terms, multi-parameter margins, etc.)", FALSE),
                    conditionalPanel(
                      condition = "input.advanced_formula == true",
                      textAreaInput("eq1_manual", "Equation 1 (manual)", rows = 3, placeholder = "y1 ~ x1 + s(x2)"),
                      textAreaInput("eq2_manual", "Equation 2 (manual)", rows = 3, placeholder = "y2 ~ x3 + x4"),
                      conditionalPanel(
                        condition = "input.copula_model == 'T' || input.copula_model == 'TSS' || input.copula_model == 'TESS'",
                        textAreaInput("eq3_manual", "Equation 3 (manual)", rows = 3, placeholder = "y3 ~ x5")
                      )
                    ),
                    hr(),
                    h4("Formula Previews"),
                    fluidRow(
                      column(4,
                             h5("Equation 1"),
                             div(class = "formula-preview", verbatimTextOutput("copula_form1"))
                      ),
                      column(4,
                             h5("Equation 2"),
                             div(class = "formula-preview", verbatimTextOutput("copula_form2"))
                      ),
                      column(4,
                             conditionalPanel(
                               condition = "input.copula_model == 'T' || input.copula_model == 'TSS' || input.copula_model == 'TESS'",
                               h5("Equation 3"),
                               div(class = "formula-preview", verbatimTextOutput("copula_form3"))
                             )
                      )
                    )
                )
              ),
              
              fluidRow(
                box(title = "Marginal Distributions", status = "primary", solidHeader = TRUE, width = 12,
                    fluidRow(
                      column(4,
                             selectInput("margin1", "Margin 1",
                                         choices = c("N", "TW", "LN", "GU", "rGU", "GP", "GPII", "GPo",
                                                     "DGP", "DGPII", "DGP0", "LO", "WEI", "iG", "GA",
                                                     "DAGUM", "SM", "BE", "FISK", "PO", "ZTP", "NBI",
                                                     "NBII", "PIG",
                                                     "probit", "logit", "cloglog", "PH", "PO"))
                      ),
                      column(4,
                             selectInput("margin2", "Margin 2",
                                         choices = c("None" = "", "N", "TW", "LN", "GU", "rGU", "GP", "GPII", "GPo",
                                                     "DGP", "DGPII", "DGP0", "LO", "WEI", "iG", "GA",
                                                     "DAGUM", "SM", "BE", "FISK", "PO", "ZTP", "NBI",
                                                     "NBII", "PIG",
                                                     "probit", "logit", "cloglog", "PH", "PO"))
                      ),
                      column(4,
                             conditionalPanel(
                               condition = "input.copula_model == 'T' || input.copula_model == 'TSS' || input.copula_model == 'TESS'",
                               selectInput("margin3", "Margin 3",
                                           choices = c("None" = "", "probit", "logit", "cloglog"))
                             )
                      )
                    )
                )
              ),
              
              fluidRow(
                box(title = "Copula Specification", status = "info", solidHeader = TRUE, width = 12,
                    selectInput("copula_type", "Copula (main)",
                                choices = c("N", "C0", "C90", "C180", "C270",
                                            "GAL0", "GAL90", "GAL180", "GAL270",
                                            "J0", "J90", "J180", "J270",
                                            "G0", "G90", "G180", "G270",
                                            "F", "AMH", "FGM", "T", "PL", "HO",
                                            "C0C90", "C0C270", "C180C90", "C180C270",
                                            "GAL0GAL90", "GAL0GAL270", "GAL180GAL90", "GAL180GAL270",
                                            "G0G90", "G0G270", "G180G90", "G180G270",
                                            "J0J90", "J0J270", "J180J90", "J180J270")),
                    conditionalPanel(
                      condition = "input.copula_model == 'ROY'",
                      selectInput("copula2", "Copula 2 (Roy model only)",
                                  choices = c("N", "C0", "C90", "C180", "C270",
                                              "GAL0", "GAL90", "GAL180", "GAL270",
                                              "J0", "J90", "J180", "J270",
                                              "G0", "G90", "G180", "G270",
                                              "F", "AMH", "FGM", "T", "PL", "HO",
                                              "C0C90", "C0C270", "C180C90", "C180C270",
                                              "GAL0GAL90", "GAL0GAL270", "GAL180GAL90", "GAL180GAL270",
                                              "G0G90", "G0G270", "G180G90", "G180G270",
                                              "J0J90", "J0J270", "J180J90", "J180J270"))
                    ),
                    conditionalPanel(
                      condition = "input.copula_type == 'T'",
                      numericInput("dof", "Degrees of Freedom (Student-t copula)", value = 3, min = 3, max = 249)
                    ),
                    conditionalPanel(
                      condition = "input.copula_model == 'ROY'",
                      numericInput("dof2", "Degrees of Freedom 2 (Roy model)", value = 3)
                    ),
                    checkboxInput("ordinal", "Ordinal model", FALSE)
                )
              ),
              
              fluidRow(
                box(title = "Estimation Options", status = "primary", solidHeader = TRUE, width = 12,
                    fluidRow(
                      column(4,
                             checkboxInput("gamlssfit", "Fit separate gamlss models first", FALSE),
                             checkboxInput("fp", "Fully parametric (unpenalised splines)", FALSE),
                             numericInput("infl.fac", "AIC inflation factor", value = 1, step = 0.1)
                      ),
                      column(4,
                             numericInput("iterlimsp", "Max smoothing parameter iterations", value = 50),
                             numericInput("tolsp", "Smoothing tolerance", value = 1e-7),
                             selectInput("extra.regI", "Extra regularisation on information matrix",
                                         choices = c("trust default" = "t", "Pivoted Cholesky" = "pC", "Symmetric Eigen" = "sED"))
                      ),
                      column(4,
                             checkboxInput("gc.l", "Frequent garbage collection (large data)", FALSE),
                             numericInput("parscale", "Parameter rescaling factor", value = NA_real_),
                             textAreaInput("knots", "Custom knots list (R syntax)", rows = 3,
                                           placeholder = "list(x1 = c(0, 0.5, 1), x2 = seq(0, 1, length = 10))")
                      )
                    ),
                    actionButton("run_copula", "Run Copula Model", 
                                 class = "btn-purple btn-block", icon = icon("link"))
                )
              ),
              
              fluidRow(
                tabBox(width = 12, title = "Copula Modeling Results",
                       tabPanel("Model Summary",
                                verbatimTextOutput("copula_summary"),
                                br(),
                                downloadButton("download_copula_fit", "Download fitted object (RDS)", class = "btn-info")
                       ),
                       tabPanel("Convergence Diagnostics",
                                verbatimTextOutput("copula_conv_check")
                       ),
                       tabPanel("Model Selection Criteria",
                                verbatimTextOutput("copula_criteria")
                       ),
                       tabPanel("Association Parameters",
                                verbatimTextOutput("copula_assoc_params")
                       ),
                       tabPanel("Marginal Diagnostics",
                                fluidRow(
                                  column(4,
                                         selectInput("copula_diag_eq", "Select Equation", choices = c("Equation 1" = "1", "Equation 2" = "2"))
                                  ),
                                  column(4,
                                         selectInput("copula_diag_type", "Plot Type",
                                                     choices = c("Smooth Terms" = "smooth",
                                                                 "Residuals vs Fitted" = "resfit",
                                                                 "Q-Q Plot" = "qq"))
                                  )
                                ),
                                plotOutput("copula_diag_plot", height = "600px")
                       ),
                       tabPanel("Copula Diagnostics",
                                fluidRow(
                                  column(6,
                                         selectInput("copula_pair", "Margin Pair", choices = "1-2")
                                  ),
                                  column(6,
                                         selectInput("copula_diag_type2", "Diagnostic Type",
                                                     choices = c("Empirical Pseudo-Observations Scatter" = "emp_scatter",
                                                                 "Dependence Parameter Smooth" = "theta_smooth"))
                                  )
                                ),
                                plotOutput("copula_diag_plot2", height = "600px"),
                                textOutput("copula_diag_note")
                       )
                )
              )
      ),
      
      # ----------------------------------------------------------------------
      # Export Tab
      # ----------------------------------------------------------------------
      tabItem(tabName = "export",
              fluidRow(
                box(width = 12, title = "Download Results", status = "success", solidHeader = TRUE,
                    tags$h4("Export Processed Data"),
                    fluidRow(
                      column(3,
                             downloadButton("download_processed_csv", "Processed Data (.csv)")
                      ),
                      column(3,
                             downloadButton("download_processed_rda", "Processed Data (.rda)")
                      ),
                      column(3,
                             downloadButton("download_processed_stata", "Processed Data (.dta)")
                      ),
                      column(3,
                             downloadButton("download_codebook", "Codebook (.pdf)")
                      )
                    ),
                    
                    tags$hr(),
                    tags$h4("Export Analysis Results"),
                    fluidRow(
                      column(3,
                             downloadButton("download_aggregated", "Country Aggregates (.csv)")
                      ),
                      column(3,
                             downloadButton("download_strategy", "Strategy Results (.zip)")
                      ),
                      column(3,
                             downloadButton("download_causal", "Causal Results (.zip)")
                      ),
                      column(3,
                             downloadButton("download_copula_results", "Copula Results (.zip)")
                      )
                    ),
                    
                    tags$hr(),
                    tags$h4("Export All Results"),
                    fluidRow(
                      column(6,
                             downloadButton("download_all", "Download All Results (.zip)", 
                                            class = "btn-success btn-lg")
                      ),
                      column(6,
                             actionButton("generate_report", "Generate Report", 
                                          class = "btn-primary btn-lg", icon = icon("file"))
                      )
                    ),
                    
                    tags$hr(),
                    tags$p("All outputs preserve original research naming for full reproducibility.")
                )
              )
      ),
      
      # ----------------------------------------------------------------------
      # Analysis Log Tab
      # ----------------------------------------------------------------------
      tabItem(tabName = "log",
              fluidRow(
                box(width = 12, title = "Analysis History & Activity Log",
                    status = "info", solidHeader = TRUE,
                    tags$p("Track all actions performed during the analysis session")
                )
              ),
              
              fluidRow(
                box(width = 12, title = "Recent Activity", status = "primary",
                    DTOutput("activity_log_table"),
                    tags$hr(),
                    fluidRow(
                      column(4,
                             actionButton("clear_log", "Clear Log", class = "btn-warning", icon = icon("trash"))
                      ),
                      column(4,
                             downloadButton("export_log", "Export Log", class = "btn-info")
                      ),
                      column(4,
                             actionButton("refresh_log", "Refresh", class = "btn-primary", icon = icon("sync"))
                      )
                    )
                )
              ),
              
              fluidRow(
                box(width = 6, title = "Session Statistics", status = "success",
                    verbatimTextOutput("session_stats")
                ),
                box(width = 6, title = "Cache Information", status = "info",
                    verbatimTextOutput("cache_info"),
                    actionButton("clear_cache", "Clear Cache", class = "btn-warning", icon = icon("broom"))
                )
              )
      )
    )
  )
)

# ==============================================================================
# Server Function - COMPLETELY REWIRED FOR FULL FUNCTIONALITY
# ==============================================================================
server <- function(input, output, session) {
  
  # Clean temp files on startup
  if(CACHE_CONFIG$auto_clean) {
    tryCatch({
      clean_temp_files(CACHE_CONFIG$directory, CACHE_CONFIG$max_age_hours)
    }, error = function(e) {
      message("Cache cleanup error: ", e$message)
    })
  }
  
  # Reactive values to store data and state
  raw_data <- reactiveVal(NULL)
  processed_data <- reactiveVal(NULL)
  aggregated_data <- reactiveVal(NULL)
  strategy_results <- reactiveVal(NULL)
  causal_results <- reactiveVal(NULL)
  copula_results <- reactiveVal(NULL)
  data_quality <- reactiveVal(NULL)
  
  # Session tracking
  analysis_log <- reactiveVal(data.frame(
    timestamp = character(),
    action = character(),
    details = character(),
    status = character(),
    stringsAsFactors = FALSE
  ))
  
  cache_hits <- reactiveVal(0)
  session_start <- Sys.time()
  
  # Helper function to log actions
  log_action <- function(action, details = "", status = "success") {
    new_entry <- create_log_entry(action, details, status)
    current_log <- analysis_log()
    analysis_log(rbind(current_log, new_entry))
  }
  
  # ----------------------------------------------------------------------
  # Data Loading
  # ----------------------------------------------------------------------
  observeEvent(input$load_sample, {
    withProgress(message = 'Loading sample data...', value = 0, {
      tryCatch({
        set.seed(123)
        n_firms <- 1000
        n_countries <- 20
        
        incProgress(0.3, detail = "Generating firms...")
        
        sample_data <- data.frame(
          id = 1:n_firms,
          iso_a3 = sample(c("USA", "GBR", "DEU", "FRA", "ITA", "ESP", "NLD", "BEL", 
                            "SWE", "NOR", "DNK", "FIN", "POL", "CZE", "HUN", "ROU", 
                            "GRC", "TUR", "EGY", "SAU"), n_firms, replace = TRUE),
          ISVI = sample(1:5, n_firms, replace = TRUE),
          FIVI = sample(1:7, n_firms, replace = TRUE),
          EMSI = sample(1:4, n_firms, replace = TRUE),
          UMSI = sample(1:3, n_firms, replace = TRUE),
          treatment = rbinom(n_firms, 1, 0.4),
          outcome = rnorm(n_firms, mean = 100, sd = 20),
          RevGrwth3 = rnorm(n_firms, mean = 10, sd = 5),
          FuelCost = rnorm(n_firms, mean = 50, sd = 15),
          ElectricityCost = rnorm(n_firms, mean = 30, sd = 10),
          laborCost = rnorm(n_firms, mean = 40, sd = 12),
          wstrict = runif(n_firms, 0.5, 2),
          EnergEffMeasAdopt = rbinom(n_firms, 1, 0.3),
          techInpMktOrient = rbinom(n_firms, 1, 0.4),
          InformalMktComp = rnorm(n_firms, mean = 2.5, sd = 1),
          Web = rbinom(n_firms, 1, 0.6),
          iQCert = rbinom(n_firms, 1, 0.2),
          ProdServInnov = rbinom(n_firms, 1, 0.25),
          ProcessInnov = rbinom(n_firms, 1, 0.2),
          m1a_trade_pos = sample(c(1:7, NA), n_firms, replace = TRUE),
          a7 = sample(c(1, 2, NA), n_firms, replace = TRUE),
          a14y = sample(c(2018:2020, NA), n_firms, replace = TRUE),
          nFulTimEmplyLFY = round(rnorm(n_firms, mean = 50, sd = 30))
        )
        
        # Make sure no columns are haven-labelled in sample data
        sample_data <- as.data.frame(sample_data)
        
        incProgress(0.6, detail = "Setting up data...")
        
        raw_data(sample_data)
        processed_data(sample_data)
        data_quality(calculate_data_quality(sample_data))
        
        incProgress(0.9, detail = "Finalizing...")
        
        log_action("Load Sample Data", "Loaded 1000 simulated firms across 20 countries")
        
        showNotification(
          "Sample data loaded successfully! (1000 simulated firms across 20 countries)", 
          type = "message",
          duration = 5
        )
      }, error = function(e) {
        log_action("Load Sample Data", e$message, "error")
        showNotification(paste("Error loading sample data:", e$message), type = "error", duration = 10)
      })
    })
  })
  
  observeEvent(input$data_upload, {
    req(input$data_upload)
    
    withProgress(message = 'Loading data...', value = 0, {
      tryCatch({
        incProgress(0.2, detail = "Validating file...")
        validate_upload(input$data_upload)
        
        incProgress(0.4, detail = "Reading file...")
        data <- load_data_safe(input$data_upload$datapath)
        
        if(requireNamespace("haven", quietly = TRUE)) {
          data <- data %>% mutate(across(where(~inherits(., "haven_labelled")), haven::as_factor))
        }
        
        incProgress(0.6, detail = "Processing data...")
        
        # Basic data cleaning
        if(nrow(data) > 0) {
          data <- data[, colSums(is.na(data)) < nrow(data)]
          
          char_cols <- sapply(data, is.character)
          if(any(char_cols)) {
            data <- data %>% mutate(across(where(is.character), as.factor))
          }
        }
        
        incProgress(0.8, detail = "Calculating quality metrics...")
        
        raw_data(data)
        processed_data(data)
        data_quality(calculate_data_quality(data))
        
        log_action("Data Upload", 
                   paste("Uploaded", input$data_upload$name, "-", 
                         nrow(data), "rows,", ncol(data), "columns"))
        
        showNotification(
          paste("Data uploaded successfully!", nrow(data), "rows,", ncol(data), "columns"), 
          type = "message",
          duration = 5
        )
      }, error = function(e) {
        log_action("Data Upload", e$message, "error")
        showNotification(paste("Error loading data:", e$message), type = "error", duration = 10)
      })
    })
  })
  
  # Update UI elements when data is loaded
  observeEvent(processed_data(), {
    df <- processed_data()
    req(df)
    
    # Original app updates
    all_vars <- names(df)
    numeric_vars <- names(df)[sapply(df, is.numeric)]
    binary_vars <- names(df)[sapply(df, function(x) length(unique(na.omit(x))) == 2)]
    
    updatePickerInput(session, "keep_vars", choices = all_vars, selected = all_vars)
    updatePickerInput(session, "nonneg_vars", choices = numeric_vars)
    updatePickerInput(session, "transform_vars", choices = numeric_vars)
    updatePickerInput(session, "binary_map_vars", choices = binary_vars)
    updatePickerInput(session, "cont_map_vars", choices = numeric_vars)
    updatePickerInput(session, "outcome_metrics", choices = numeric_vars)
    
    # Causal inference updates
    binary_candidates <- names(df)[sapply(df, function(x) {
      vals <- na.omit(unique(x))
      length(vals) == 2 && all(vals %in% c(0, 1))
    })]
    updateSelectInput(session, "treatment_var", choices = c("", binary_candidates))
    
    updateSelectInput(session, "causal_outcome", choices = c("", numeric_vars))
    updatePickerInput(session, "causal_covars", choices = all_vars)
    
    # NEW: Copula modeling updates
    updateSelectInput(session, "resp1", choices = c("Choose..." = "", all_vars))
    updateSelectInput(session, "resp2", choices = c("Choose..." = "", all_vars))
    updateSelectInput(session, "resp3", choices = c("Choose..." = "", all_vars))
    
    updateSelectizeInput(session, "preds1_lin", choices = all_vars, server = TRUE)
    updateSelectizeInput(session, "preds1_sm", choices = all_vars, server = TRUE)
    updateSelectizeInput(session, "preds2_lin", choices = all_vars, server = TRUE)
    updateSelectizeInput(session, "preds2_sm", choices = all_vars, server = TRUE)
    updateSelectizeInput(session, "preds3_lin", choices = all_vars, server = TRUE)
    updateSelectizeInput(session, "preds3_sm", choices = all_vars, server = TRUE)
  })
  
  # ----------------------------------------------------------------------
  # Data Preprocessing
  # ----------------------------------------------------------------------
  observeEvent(input$apply_filter, {
    req(raw_data())
    
    withProgress(message = 'Applying filters...', value = 0, {
      tryCatch({
        df <- raw_data()
        
        incProgress(0.3, detail = "Selecting variables...")
        
        if(length(input$keep_vars) > 0) {
          df <- df %>% select(all_of(input$keep_vars))
        }
        
        incProgress(0.5, detail = "Applying non-negative filter...")
        
        if(length(input$nonneg_vars) > 0) {
          df <- df %>% filter(if_all(all_of(input$nonneg_vars), ~ .x >= 0 | is.na(.x)))
        }
        
        incProgress(0.7, detail = "Removing missing values...")
        
        if(input$remove_missing) {
          df <- df %>% filter(complete.cases(.))
        }
        
        incProgress(0.9, detail = "Updating quality metrics...")
        
        processed_data(df)
        data_quality(calculate_data_quality(df))
        
        log_action("Apply Filtering", paste("Filtered to", nrow(df), "rows,", ncol(df), "columns"))
        showNotification("Filtering applied successfully!", type = "message")
        
      }, error = function(e) {
        log_action("Apply Filtering", e$message, "error")
        showNotification(paste("Error applying filters:", e$message), type = "error")
      })
    })
  })
  
  observeEvent(input$apply_recodes, {
    req(processed_data())
    
    withProgress(message = 'Applying recodes...', value = 0, {
      tryCatch({
        df <- processed_data()
        
        incProgress(0.2, detail = "Processing standard recodes...")
        
        if("trade_pos" %in% input$recodes && "m1a_trade_pos" %in% names(df)) {
          df <- df %>% mutate(m1a_trade_pos = replace_na(m1a_trade_pos, 8))
        }
        
        if("dates" %in% input$recodes) {
          if("a14d" %in% names(df)) df <- df %>% mutate(a14d = replace_na(a14d, 16))
          if("a14m" %in% names(df)) df <- df %>% mutate(a14m = replace_na(a14m, 4))
          if("a14y" %in% names(df)) df <- df %>% mutate(a14y = replace_na(a14y, 2019))
        }
        
        incProgress(0.4, detail = "Processing foreign ownership...")
        
        if("foreign" %in% input$recodes && "a7" %in% names(df)) {
          df <- df %>% mutate(
            a7 = if_else(a7 == 2, 0, 1),
            a7 = replace_na(a7, 0)
          )
        }
        
        if("country_code" %in% input$recodes && "country" %in% names(df) && !"iso_a3" %in% names(df)) {
          df <- df %>% mutate(
            iso_a3 = countrycode(country, "country.name", "iso3c")
          )
        }
        
        incProgress(0.6, detail = "Standardizing weights...")
        
        if("weights" %in% input$recodes && "wstrict" %in% names(df)) {
          df <- df %>% mutate(
            wstrict = replace_na(wstrict, 1),
            wstrict = if_else(wstrict <= 0, 1, wstrict)
          )
        }
        
        incProgress(0.8, detail = "Applying custom mutations...")
        
        if(nzchar(input$custom_mutate)) {
          exprs <- sanitize_mutate(input$custom_mutate)
          if(!is.null(exprs)) {
            for (e in exprs) {
              tryCatch({
                df <- df %>% mutate(!!rlang::parse_expr(e))
              }, error = function(err) {
                showNotification(paste("Error in expression:", e, "-", err$message), type = "error")
              })
            }
          }
        }
        
        processed_data(df)
        data_quality(calculate_data_quality(df))
        
        log_action("Apply Recodes", paste("Applied", length(input$recodes), "standard recodes"))
        showNotification("Recodes and mutations applied successfully!", type = "message")
        
      }, error = function(e) {
        log_action("Apply Recodes", e$message, "error")
        showNotification(paste("Error applying recodes:", e$message), type = "error")
      })
    })
  })
  
  observeEvent(input$apply_transform, {
    req(processed_data(), input$transform_vars, input$transform_type)
    
    withProgress(message = 'Applying transformations...', value = 0, {
      tryCatch({
        df <- processed_data()
        
        for(i in seq_along(input$transform_vars)) {
          var <- input$transform_vars[i]
          incProgress(i/length(input$transform_vars), detail = paste("Transforming", var, "..."))
          
          if(var %in% names(df) && is.numeric(df[[var]])) {
            new_name <- paste0(var, "_", input$transform_type)
            
            if(input$transform_type == "log") {
              df[[new_name]] <- log(df[[var]] + 1)
            } else if(input$transform_type == "zscore") {
              df[[new_name]] <- scale(df[[var]])
            } else if(input$transform_type == "normalize") {
              min_val <- min(df[[var]], na.rm = TRUE)
              max_val <- max(df[[var]], na.rm = TRUE)
              if(max_val > min_val) {
                df[[new_name]] <- (df[[var]] - min_val) / (max_val - min_val)
              }
            } else if(input$transform_type == "sqrt") {
              df[[new_name]] <- sqrt(abs(df[[var]]))
            } else if(input$transform_type == "asinh") {
              df[[new_name]] <- asinh(df[[var]])
            }
          }
        }
        
        processed_data(df)
        data_quality(calculate_data_quality(df))
        
        log_action("Apply Transformation", 
                   paste("Transformed", length(input$transform_vars), "variables using", input$transform_type))
        showNotification("Transformations applied successfully!", type = "message")
        
      }, error = function(e) {
        log_action("Apply Transformation", e$message, "error")
        showNotification(paste("Error applying transformations:", e$message), type = "error")
      })
    })
  })
  
  # ----------------------------------------------------------------------
  # Preprocessing Outputs
  # ----------------------------------------------------------------------
  output$data_summary <- renderPrint({
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    req(df)
    
    cat("Data Summary\n")
    cat("============\n")
    cat("Observations:", nrow(df), "\n")
    cat("Variables:", ncol(df), "\n")
    cat("\nVariable types:\n")
    type_counts <- table(sapply(df, function(x) class(x)[1]))
    print(type_counts)
    cat("\nMissing values:", sum(is.na(df)), "\n")
    cat("Complete rows:", sum(complete.cases(df)), "\n")
  })
  
  output$data_dimensions <- renderText({
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    req(df)
    paste(nrow(df), "rows ×", ncol(df), "columns")
  })
  
  output$quality_score_text <- renderText({
    dq <- data_quality()
    if(!is.null(dq)) {
      paste0(round(100 - dq$summary$missing_pct, 1), "%")
    } else {
      "N/A"
    }
  })
  
  output$processed_table <- renderDT({
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    req(df)
    datatable(df, 
              options = list(scrollX = TRUE, pageLength = 10), 
              filter = "top",
              rownames = FALSE)
  })
  
  output$missing_plot <- renderPlotly({
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    req(df)
    
    missing_counts <- colSums(is.na(df))
    missing_df <- data.frame(
      Variable = names(missing_counts),
      Missing = as.numeric(missing_counts),
      Proportion = as.numeric(missing_counts) / nrow(df)
    ) %>% arrange(desc(Missing))
    
    plot_ly(missing_df[1:min(20, nrow(missing_df)),], 
            x = ~Variable, y = ~Proportion * 100, 
            type = "bar", 
            marker = list(color = VIZ_CONFIG$default_colors[1])) %>%
      layout(title = "Missing Values by Variable (Top 20)",
             yaxis = list(title = "Percentage Missing"),
             xaxis = list(title = "", tickangle = 45))
  })
  
  output$missing_table <- renderDT({
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    req(df)
    
    missing_counts <- colSums(is.na(df))
    missing_df <- data.frame(
      Variable = names(missing_counts),
      Missing = as.numeric(missing_counts),
      Proportion = paste0(round(as.numeric(missing_counts) / nrow(df) * 100, 2), "%"),
      Type = sapply(df, function(x) class(x)[1])
    ) %>% arrange(desc(Missing))
    
    datatable(missing_df, 
              options = list(pageLength = 10),
              rownames = FALSE)
  })
  
  output$var_summary <- renderDT({
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    req(df)
    
    # Create summary data frame safely
    summary_df <- data.frame(
      Variable = names(df),
      Type = sapply(df, function(x) class(x)[1]),
      Missing = colSums(is.na(df)),
      Unique = sapply(df, function(x) length(unique(na.omit(x)))),
      stringsAsFactors = FALSE
    )
    
    # Add Mean and SD only for numeric columns
    # Initialize columns with NA
    summary_df$Mean <- NA_real_
    summary_df$SD <- NA_real_
    
    # Calculate for numeric columns only
    numeric_cols <- sapply(df, is.numeric)
    if(any(numeric_cols)) {
      # Calculate means for numeric columns
      means <- sapply(df[, numeric_cols, drop = FALSE], 
                      function(x) round(mean(x, na.rm = TRUE), 2))
      
      # Calculate SDs for numeric columns
      sds <- sapply(df[, numeric_cols, drop = FALSE], 
                    function(x) round(sd(x, na.rm = TRUE), 2))
      
      # Assign values to the correct rows
      summary_df$Mean[numeric_cols] <- means
      summary_df$SD[numeric_cols] <- sds
    }
    
    # Handle factor/character columns - show most frequent value instead
    factor_char_cols <- sapply(df, function(x) is.factor(x) | is.character(x))
    if(any(factor_char_cols)) {
      # Create Mode column for categorical variables
      summary_df$Mode <- NA_character_
      
      for(i in which(factor_char_cols)) {
        tab <- table(df[[i]], useNA = "no")
        if(length(tab) > 0) {
          summary_df$Mode[i] <- names(which.max(tab))[1]
        }
      }
    }
    
    datatable(summary_df, 
              options = list(pageLength = 15, scrollX = TRUE),
              rownames = FALSE,
              escape = FALSE) %>%
      formatRound(columns = c('Mean', 'SD'), digits = 2)
  })
  
  output$dist_plots <- renderPlotly({
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    req(df)
    
    num_vars <- names(df)[sapply(df, is.numeric)]
    if(length(num_vars) == 0) return(NULL)
    
    plot_vars <- head(num_vars, 6)
    plots <- list()
    
    for(i in seq_along(plot_vars)) {
      var <- plot_vars[i]
      p <- plot_ly(df, x = ~get(var), type = "histogram", 
                   nbinsx = 30,
                   marker = list(color = VIZ_CONFIG$default_colors[i %% 5 + 1])) %>%
        layout(title = var, xaxis = list(title = ""))
      plots[[i]] <- p
    }
    
    subplot(plots, nrows = 2, shareX = FALSE, shareY = FALSE)
  })
  
  output$correlation_matrix <- renderPlotly({
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    req(df)
    
    numeric_data <- df %>% 
      select(where(is.numeric)) %>%
      select(1:min(15, ncol(.)))
    
    if(ncol(numeric_data) < 2) {
      return(NULL)
    }
    
    cor_matrix <- cor(numeric_data, use = "pairwise.complete.obs")
    
    plot_ly(z = cor_matrix, 
            x = colnames(cor_matrix), 
            y = rownames(cor_matrix),
            type = "heatmap",
            colors = colorRamp(c("blue", "white", "red")),
            zmin = -1, zmax = 1) %>%
      layout(title = "Correlation Matrix",
             xaxis = list(tickangle = -45),
             margin = list(b = 100, l = 100))
  })
  
  # ----------------------------------------------------------------------
  # Data Quality Outputs
  # ----------------------------------------------------------------------
  output$quality_completeness <- renderValueBox({
    dq <- data_quality()
    pct <- if(!is.null(dq)) 100 - dq$summary$missing_pct else 0
    
    valueBox(
      paste0(round(pct, 1), "%"),
      "Data Completeness",
      icon = icon("check"),
      color = if(pct >= 80) "green" else if(pct >= 60) "yellow" else "red"
    )
  })
  
  output$quality_missing <- renderValueBox({
    dq <- data_quality()
    pct <- if(!is.null(dq)) dq$summary$missing_pct else 0
    
    valueBox(
      paste0(round(pct, 1), "%"),
      "Missing Data",
      icon = icon("exclamation-triangle"),
      color = if(pct <= 20) "green" else if(pct <= 40) "yellow" else "red"
    )
  })
  
  output$quality_numeric <- renderValueBox({
    dq <- data_quality()
    count <- if(!is.null(dq)) dq$summary$numeric_vars else 0
    
    valueBox(
      count,
      "Numeric Variables",
      icon = icon("hashtag"),
      color = "blue"
    )
  })
  
  output$quality_categorical <- renderValueBox({
    dq <- data_quality()
    count <- if(!is.null(dq)) dq$summary$factor_vars + dq$summary$char_vars else 0
    
    valueBox(
      count,
      "Categorical Variables",
      icon = icon("tags"),
      color = "purple"
    )
  })
  
  output$quality_missing_plot <- renderPlotly({
    dq <- data_quality()
    req(dq)
    
    var_quality <- dq$variables %>%
      arrange(desc(Missing_Pct)) %>%
      head(20)
    
    plot_ly(var_quality, 
            x = ~Missing_Pct, 
            y = ~reorder(Variable, Missing_Pct),
            type = 'bar', 
            orientation = 'h',
            marker = list(color = ~Missing_Pct, 
                          colorscale = list(c(0, 'green'), c(0.5, 'yellow'), c(1, 'red')),
                          showscale = FALSE)) %>%
      layout(title = "Top 20 Variables by Missing Data %",
             xaxis = list(title = "Missing %"),
             yaxis = list(title = ""),
             margin = list(l = 150))
  })
  
  output$vartype_plot <- renderPlotly({
    dq <- data_quality()
    req(dq)
    
    type_counts <- data.frame(
      Type = c("Numeric", "Factor", "Character"),
      Count = c(dq$summary$numeric_vars,
                dq$summary$factor_vars,
                dq$summary$char_vars)
    )
    
    plot_ly(type_counts, 
            labels = ~Type, 
            values = ~Count, 
            type = 'pie',
            marker = list(colors = VIZ_CONFIG$default_colors)) %>%
      layout(title = "Variable Types Distribution")
  })
  
  output$quality_table <- renderDT({
    dq <- data_quality()
    req(dq)
    
    datatable(dq$variables,
              options = list(pageLength = 15, scrollX = TRUE),
              filter = 'top',
              rownames = FALSE) %>%
      formatStyle('Missing_Pct',
                  backgroundColor = styleInterval(c(20, 40), 
                                                  c('lightgreen', 'lightyellow', 'lightcoral')))
  })
  
  output$quality_recommendations <- renderUI({
    dq <- data_quality()
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    req(dq, df)
    
    recommendations <- list()
    
    if(dq$summary$missing_pct > 20) {
      recommendations <- c(recommendations,
                           tags$li(class = "text-warning", 
                                   icon("exclamation-triangle"),
                                   " High missing data detected. Consider imputation or removal of incomplete cases."))
    }
    
    high_missing_vars <- dq$variables %>%
      filter(Missing_Pct > 50) %>%
      nrow()
    
    if(high_missing_vars > 0) {
      recommendations <- c(recommendations,
                           tags$li(class = "text-danger",
                                   icon("times-circle"),
                                   paste0(" ", high_missing_vars, " variables have >50% missing data. Consider dropping these variables.")))
    }
    
    if(dq$summary$complete_rows < nrow(df) * 0.5) {
      recommendations <- c(recommendations,
                           tags$li(class = "text-warning",
                                   icon("info-circle"),
                                   " Less than 50% of rows are complete. Multiple imputation may be beneficial."))
    }
    
    if(length(recommendations) == 0) {
      recommendations <- list(
        tags$li(class = "text-success",
                icon("check-circle"),
                " Data quality is good! No major issues detected.")
      )
    }
    
    tags$ul(recommendations)
  })
  
  # ----------------------------------------------------------------------
  # Home Page Value Boxes
  # ----------------------------------------------------------------------
  output$total_firms <- renderValueBox({
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    
    count <- if(!is.null(df)) nrow(df) else 0
    valueBox(
      value = format(count, big.mark = ","),
      subtitle = "Total Firms",
      icon = icon("building"),
      color = "aqua"
    )
  })
  
  output$total_countries <- renderValueBox({
    df <- processed_data()
    if(is.null(df)) df <- raw_data()
    
    count <- if(!is.null(df) && "iso_a3" %in% names(df)) {
      length(unique(na.omit(df$iso_a3)))
    } else 0
    
    valueBox(
      value = count,
      subtitle = "Countries",
      icon = icon("globe"),
      color = "green"
    )
  })
  
  output$data_quality_score <- renderValueBox({
    dq <- data_quality()
    score <- if(!is.null(dq)) {
      100 - dq$summary$missing_pct
    } else 0
    
    color <- if(score >= 80) "green" else if(score >= 60) "yellow" else "red"
    
    valueBox(
      value = paste0(round(score, 1), "%"),
      subtitle = "Data Quality Score",
      icon = icon("check-circle"),
      color = color
    )
  })
  
  output$last_action <- renderInfoBox({
    log <- analysis_log()
    last_log <- if(nrow(log) > 0) {
      tail(log, 1)
    } else {
      data.frame(action = "No actions yet", timestamp = Sys.time())
    }
    
    infoBox(
      "Last Action",
      last_log$action,
      icon = icon("history"),
      color = "blue",
      fill = TRUE
    )
  })
  
  output$cache_status <- renderInfoBox({
    infoBox(
      "Cache Hits",
      cache_hits(),
      icon = icon("database"),
      color = "purple",
      fill = TRUE
    )
  })
  
  output$analysis_count <- renderInfoBox({
    count <- nrow(analysis_log())
    infoBox(
      "Total Analyses",
      count,
      icon = icon("chart-line"),
      color = "orange",
      fill = TRUE
    )
  })
  
  # ----------------------------------------------------------------------
  # Spatial Mapping
  # ----------------------------------------------------------------------
  observeEvent(input$run_aggregation, {
    req(processed_data())
    
    withProgress(message = 'Aggregating data...', value = 0, {
      tryCatch({
        pov14 <- processed_data()
        
        if(!"iso_a3" %in% names(pov14)) {
          showNotification("Error: iso_a3 variable not found. Please create country codes in preprocessing.", 
                           type = "error")
          return()
        }
        
        incProgress(0.3, detail = "Computing weighted statistics...")
        
        weight_var <- if(input$weight_var != "none" && input$weight_var %in% names(pov14)) {
          pov14[[input$weight_var]]
        } else {
          rep(1, nrow(pov14))
        }
        
        wtd_stats <- function(x, w) {
          valid <- !is.na(x) & !is.na(w)
          if(sum(valid) == 0) return(c(mean = NA, sd = NA))
          
          x_valid <- x[valid]
          w_valid <- w[valid]
          
          mean_val <- sum(x_valid * w_valid) / sum(w_valid)
          
          if(length(x_valid) > 1) {
            var_val <- sum(w_valid * (x_valid - mean_val)^2) / sum(w_valid)
            sd_val <- sqrt(var_val)
          } else {
            sd_val <- 0
          }
          
          c(mean = mean_val, sd = sd_val)
        }
        
        incProgress(0.5, detail = "Aggregating by country...")
        
        agg <- pov14 %>%
          group_by(iso_a3) %>%
          summarise(count = n(), .groups = "drop")
        
        if(length(input$binary_map_vars) > 0) {
          binary_agg <- pov14 %>%
            group_by(iso_a3) %>%
            summarise(
              across(all_of(input$binary_map_vars), 
                     ~ mean(.x, na.rm = TRUE) * 100, 
                     .names = "p{.col}")
            )
          agg <- left_join(agg, binary_agg, by = "iso_a3")
        }
        
        if(length(input$cont_map_vars) > 0) {
          cont_agg <- pov14 %>%
            group_by(iso_a3) %>%
            summarise(
              across(all_of(input$cont_map_vars),
                     ~ wtd_stats(.x, weight_var)["mean"],
                     .names = "Avrg{.col}"),
              across(all_of(input$cont_map_vars),
                     ~ wtd_stats(.x, weight_var)["sd"],
                     .names = "Sd{.col}"),
              .groups = "drop"
            )
          agg <- left_join(agg, cont_agg, by = "iso_a3")
        }
        
        incProgress(0.9, detail = "Finalizing...")
        
        aggregated_data(agg)
        log_action("Run Aggregation", paste("Aggregated data for", nrow(agg), "countries"))
        showNotification("Aggregation completed successfully!", type = "message")
        
      }, error = function(e) {
        log_action("Run Aggregation", e$message, "error")
        showNotification(paste("Error in aggregation:", e$message), type = "error")
      })
    })
  })
  
  output$tmap_plot <- renderTmap({
    req(aggregated_data())
    
    agg <- aggregated_data()
    tryCatch({
      data("World", package = "tmap")
      Global_map <- World %>% 
        mutate(iso_a3 = iso_a3) %>% 
        select(iso_a3, geometry)
      
      map_data <- Global_map %>% left_join(agg, by = "iso_a3")
      
      # Select mapping variables
      map_vars <- names(agg)[sapply(agg, is.numeric)]
      map_vars <- setdiff(map_vars, "count") # Exclude count if not needed
      map_vars <- head(map_vars, 6) # Limit to 6 variables for readability
      
      # Create tmap object
      tm <- tm_shape(map_data) +
        tm_polygons(map_vars,
                    style = "quantile",
                    palette = input$color_palette,
                    n = 5,
                    title = map_vars)
      
      # Return tmap object for renderTmap
      tm
      
    }, error = function(e) {
      showNotification(paste("Error rendering map:", e$message), type = "error")
      # Return a simple tmap in case of error
      tm_shape(sf::st_sf(geometry = sf::st_sfc())) +
        tm_layout(title = "Error loading map data")
    })
  })
  
  output$static_map <- renderPlotly({
    req(aggregated_data())
    
    agg <- aggregated_data()
    
    plot_ly(agg, type = 'choropleth', locations = ~iso_a3,
            locationmode = 'ISO-3', z = ~count,
            colorscale = 'Viridis') %>%
      layout(title = "Firm Count by Country",
             geo = list(projection = list(type = 'natural earth')))
  })
  
  output$choropleth_map <- renderPlotly({
    req(aggregated_data())
    
    agg <- aggregated_data()
    num_cols <- names(agg)[sapply(agg, is.numeric)]
    if(length(num_cols) > 1) {
      z_var <- num_cols[2]
    } else {
      z_var <- "count"
    }
    
    plot_ly(agg, type = 'choropleth', locations = ~iso_a3,
            locationmode = 'ISO-3', z = ~get(z_var),
            colorscale = 'RdYlGn') %>%
      layout(title = paste("Map of", z_var),
             geo = list(projection = list(type = 'natural earth')))
  })
  
  output$agg_table <- renderDT({
    req(aggregated_data())
    datatable(aggregated_data(), 
              options = list(scrollX = TRUE, pageLength = 15),
              rownames = FALSE)
  })
  
  output$region_table <- renderDT({
    req(aggregated_data())
    
    agg <- aggregated_data()
    
    region_summary <- data.frame(
      Metric = c("Total Countries", "Total Firms", "Avg Firms per Country"),
      Value = c(nrow(agg),
                sum(agg$count, na.rm = TRUE),
                round(mean(agg$count, na.rm = TRUE), 1))
    )
    
    datatable(region_summary, options = list(dom = 't'), rownames = FALSE)
  })
  
  output$map_data_preview <- renderDT({
    req(aggregated_data())
    datatable(head(aggregated_data(), 10), 
              options = list(scrollX = TRUE, dom = 't'),
              rownames = FALSE)
  })
  
  output$download_map_data <- downloadHandler(
    filename = function() {
      paste0("map_data_", Sys.Date(), ".csv")
    },
    content = function(file) {
      write.csv(aggregated_data(), file, row.names = FALSE)
    }
  )
  
  # ----------------------------------------------------------------------
  # Strategy Effectiveness Analysis
  # ----------------------------------------------------------------------
  observeEvent(input$run_strategy_analysis, {
    req(processed_data(), input$strategy_var, input$outcome_metrics)
    
    withProgress(message = 'Running strategy analysis...', value = 0, {
      tryCatch({
        pov14 <- processed_data()
        strat_var <- input$strategy_var
        outcome_vars <- input$outcome_metrics
        
        if(!(strat_var %in% names(pov14))) {
          showNotification("Strategy variable not found in data", type = "error")
          return()
        }
        
        incProgress(0.2, detail = "Computing aggregates...")
        
        wt <- if(input$use_weights && "wstrict" %in% names(pov14)) {
          pov14$wstrict
        } else {
          rep(1, nrow(pov14))
        }
        
        agg <- pov14 %>%
          group_by(.data[[strat_var]]) %>%
          summarise(
            count = n(),
            across(all_of(outcome_vars[outcome_vars %in% names(pov14)]),
                   list(
                     mean = ~ mean(.x, na.rm = TRUE),
                     sd = ~ sd(.x, na.rm = TRUE)
                   ),
                   .names = "{.fn}_{.col}"),
            .groups = "drop"
          ) %>%
          rename(strategy = 1)
        
        incProgress(0.4, detail = "Computing statistics...")
        
        mean_cols <- grep("^mean_", names(agg), value = TRUE)
        
        if(length(mean_cols) > 0) {
          Y <- as.matrix(agg[, mean_cols])
          rownames(Y) <- agg$strategy
        } else {
          Y <- NULL
        }
        
        incProgress(0.6, detail = "Computing pareto frontier...")
        
        pareto_optimal <- rep(FALSE, nrow(agg))
        if(!is.null(Y) && nrow(Y) > 1) {
          for(i in 1:nrow(Y)) {
            dominated <- FALSE
            for(j in 1:nrow(Y)) {
              if(i != j) {
                if(all(Y[j,] >= Y[i,]) && any(Y[j,] > Y[i,])) {
                  dominated <- TRUE
                  break
                }
              }
            }
            pareto_optimal[i] <- !dominated
          }
        }
        agg$pareto_optimal <- pareto_optimal
        
        incProgress(0.8, detail = "Running PCA and entropy...")
        
        pca_result <- NULL
        entropy_result <- NULL
        
        if(!is.null(Y) && nrow(Y) >= 3 && ncol(Y) >= 2) {
          Y_scaled <- scale(Y)
          pca_result <- prcomp(Y_scaled, center = FALSE, scale. = FALSE)
          
          Y_norm <- t(apply(abs(Y), 1, function(x) x / sum(x, na.rm = TRUE)))
          entropy_result <- apply(Y_norm, 1, function(x) {
            x <- x[x > 0]
            -sum(x * log(x))
          })
        }
        
        incProgress(0.95, detail = "Finalizing...")
        
        results <- list(
          agg = agg,
          Y = Y,
          pareto_optimal = pareto_optimal,
          pca = pca_result,
          entropy = entropy_result,
          strategy_var = strat_var,
          outcome_vars = outcome_vars
        )
        
        strategy_results(results)
        log_action("Strategy Analysis", 
                   paste("Evaluated", strat_var, "across", length(outcome_vars), "outcomes"))
        showNotification("Strategy analysis completed!", type = "message")
        
      }, error = function(e) {
        log_action("Strategy Analysis", e$message, "error")
        showNotification(paste("Error in strategy analysis:", e$message), type = "error")
      })
    })
  })
  
  # Strategy outputs
  output$total_strategies <- renderValueBox({
    res <- strategy_results()
    count <- if(!is.null(res)) nrow(res$agg) else 0
    valueBox(count, "Total Strategies", icon = icon("layer-group"), color = "red")
  })
  
  output$pareto_count <- renderValueBox({
    res <- strategy_results()
    count <- if(!is.null(res)) sum(res$pareto_optimal) else 0
    valueBox(count, "Pareto Optimal", icon = icon("star"), color = "yellow")
  })
  
  output$best_strategy <- renderValueBox({
    res <- strategy_results()
    best <- if(!is.null(res) && !is.null(res$Y) && nrow(res$Y) > 0) {
      res$agg$strategy[which.max(rowMeans(res$Y, na.rm = TRUE))]
    } else "N/A"
    valueBox(best, "Best Overall", icon = icon("trophy"), color = "green")
  })
  
  output$freq_table <- renderDT({
    req(strategy_results())
    res <- strategy_results()
    
    freq_df <- res$agg %>%
      select(strategy, count) %>%
      mutate(percentage = round(count / sum(count) * 100, 2))
    
    datatable(freq_df, 
              options = list(pageLength = 10),
              rownames = FALSE)
  })
  
  output$freq_bar <- renderPlotly({
    req(strategy_results())
    res <- strategy_results()
    
    plot_ly(res$agg, x = ~strategy, y = ~count, type = "bar",
            marker = list(color = VIZ_CONFIG$default_colors[1])) %>%
      layout(title = "Strategy Frequency Distribution",
             xaxis = list(title = "Strategy"),
             yaxis = list(title = "Count"))
  })
  
  output$desc_table <- renderDT({
    req(strategy_results())
    datatable(strategy_results()$agg, 
              options = list(scrollX = TRUE, pageLength = 10),
              rownames = FALSE)
  })
  
  output$desc_boxplot <- renderPlotly({
    req(strategy_results(), processed_data())
    res <- strategy_results()
    df <- processed_data()
    
    if(length(res$outcome_vars) > 0 && res$outcome_vars[1] %in% names(df)) {
      outcome <- res$outcome_vars[1]
      
      plot_ly(df, x = ~as.factor(get(res$strategy_var)), y = ~get(outcome),
              type = "box", color = ~as.factor(get(res$strategy_var))) %>%
        layout(title = paste("Distribution of", outcome, "by Strategy"),
               xaxis = list(title = "Strategy"),
               yaxis = list(title = outcome),
               showlegend = FALSE)
    } else {
      plotly_empty()
    }
  })
  
  output$volatility_plot <- renderPlotly({
    req(strategy_results())
    res <- strategy_results()
    
    sd_cols <- grep("^sd_", names(res$agg), value = TRUE)
    if(length(sd_cols) > 0) {
      vol_data <- res$agg %>%
        select(strategy, all_of(sd_cols)) %>%
        pivot_longer(cols = -strategy, names_to = "metric", values_to = "volatility")
      
      plot_ly(vol_data, x = ~strategy, y = ~volatility, color = ~metric,
              type = "bar") %>%
        layout(title = "Volatility by Strategy",
               xaxis = list(title = "Strategy"),
               yaxis = list(title = "Standard Deviation"),
               barmode = "group")
    } else {
      plotly_empty()
    }
  })
  
  output$volatility_table <- renderDT({
    req(strategy_results())
    res <- strategy_results()
    
    sd_cols <- grep("^sd_", names(res$agg), value = TRUE)
    if(length(sd_cols) > 0) {
      vol_df <- res$agg %>% select(strategy, all_of(sd_cols))
      datatable(vol_df, 
                options = list(scrollX = TRUE),
                rownames = FALSE)
    }
  })
  
  output$stat_tests <- renderPrint({
    req(strategy_results(), processed_data())
    res <- strategy_results()
    df <- processed_data()
    
    cat("Statistical Tests for Strategy Effectiveness\n")
    cat("=============================================\n\n")
    
    if(length(res$outcome_vars) > 0) {
      for(outcome in res$outcome_vars[1:min(3, length(res$outcome_vars))]) {
        if(outcome %in% names(df)) {
          cat("Outcome:", outcome, "\n")
          cat("---------\n")
          
          formula <- as.formula(paste(outcome, "~", res$strategy_var))
          aov_result <- aov(formula, data = df)
          print(summary(aov_result))
          cat("\n")
        }
      }
    }
  })
  
  output$test_plots <- renderPlotly({
    req(strategy_results(), processed_data())
    res <- strategy_results()
    df <- processed_data()
    
    if(length(res$outcome_vars) > 0 && res$outcome_vars[1] %in% names(df)) {
      outcome <- res$outcome_vars[1]
      
      means <- df %>%
        group_by(.data[[res$strategy_var]]) %>%
        summarise(
          mean = mean(.data[[outcome]], na.rm = TRUE),
          se = sd(.data[[outcome]], na.rm = TRUE) / sqrt(n()),
          .groups = "drop"
        )
      
      plot_ly(means, x = ~get(res$strategy_var), y = ~mean,
              type = "scatter", mode = "markers",
              error_y = list(array = ~se * 1.96),
              marker = list(size = 12, color = VIZ_CONFIG$default_colors[2])) %>%
        layout(title = paste("Mean", outcome, "with 95% CI"),
               xaxis = list(title = "Strategy"),
               yaxis = list(title = paste("Mean", outcome)))
    } else {
      plotly_empty()
    }
  })
  
  output$dominance_heatmap <- renderPlotly({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$Y) && nrow(res$Y) > 1) {
      n <- nrow(res$Y)
      dom_matrix <- matrix(0, n, n)
      rownames(dom_matrix) <- rownames(res$Y)
      colnames(dom_matrix) <- rownames(res$Y)
      
      for(i in 1:n) {
        for(j in 1:n) {
          if(i != j) {
            if(all(res$Y[i,] >= res$Y[j,]) && any(res$Y[i,] > res$Y[j,])) {
              dom_matrix[i, j] <- 1
            }
          }
        }
      }
      
      plot_ly(z = dom_matrix, x = colnames(dom_matrix), y = rownames(dom_matrix),
              type = "heatmap", colors = c("white", "green")) %>%
        layout(title = "Dominance Matrix (1 = row dominates column)",
               xaxis = list(title = ""),
               yaxis = list(title = ""))
    } else {
      plotly_empty()
    }
  })
  
  output$dominance_matrix <- renderDT({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$Y) && nrow(res$Y) > 1) {
      n <- nrow(res$Y)
      dom_matrix <- matrix(0, n, n)
      rownames(dom_matrix) <- rownames(res$Y)
      colnames(dom_matrix) <- rownames(res$Y)
      
      for(i in 1:n) {
        for(j in 1:n) {
          if(i != j) {
            if(all(res$Y[i,] >= res$Y[j,]) && any(res$Y[i,] > res$Y[j,])) {
              dom_matrix[i, j] <- 1
            }
          }
        }
      }
      
      datatable(as.data.frame(dom_matrix), 
                options = list(scrollX = TRUE),
                rownames = TRUE)
    }
  })
  
  output$dominance_network <- renderVisNetwork({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$Y) && nrow(res$Y) > 1) {
      n <- nrow(res$Y)
      strategies <- rownames(res$Y)
      
      nodes <- data.frame(
        id = 1:n,
        label = strategies,
        color = ifelse(res$pareto_optimal, "gold", "lightblue"),
        shape = "circle"
      )
      
      edges <- data.frame(from = integer(), to = integer())
      for(i in 1:n) {
        for(j in 1:n) {
          if(i != j) {
            if(all(res$Y[i,] >= res$Y[j,]) && any(res$Y[i,] > res$Y[j,])) {
              edges <- rbind(edges, data.frame(from = i, to = j))
            }
          }
        }
      }
      
      if(nrow(edges) > 0) {
        visNetwork(nodes, edges) %>%
          visEdges(arrows = "to") %>%
          visLayout(randomSeed = 123) %>%
          visOptions(highlightNearest = TRUE)
      }
    }
  })
  
  output$pareto_table <- renderDT({
    req(strategy_results())
    res <- strategy_results()
    
    pareto_df <- res$agg %>%
      filter(pareto_optimal) %>%
      select(strategy, everything())
    
    datatable(pareto_df, 
              options = list(scrollX = TRUE),
              rownames = FALSE)
  })
  
  output$pareto_plot <- renderPlotly({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$Y) && ncol(res$Y) >= 2) {
      plot_data <- data.frame(
        strategy = rownames(res$Y),
        x = res$Y[,1],
        y = res$Y[,2],
        pareto = res$pareto_optimal
      )
      
      plot_ly(plot_data, x = ~x, y = ~y, text = ~strategy,
              type = "scatter", mode = "markers+text",
              color = ~pareto, colors = c("lightblue", "gold"),
              marker = list(size = 12),
              textposition = "top center") %>%
        layout(title = "Pareto Frontier",
               xaxis = list(title = colnames(res$Y)[1]),
               yaxis = list(title = colnames(res$Y)[2]))
    } else {
      plotly_empty()
    }
  })
  
  output$pareto_radar <- renderPlotly({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$Y) && sum(res$pareto_optimal) > 0 && ncol(res$Y) >= 3) {
      pareto_Y <- res$Y[res$pareto_optimal, , drop = FALSE]
      
      if(nrow(pareto_Y) > 0 && ncol(pareto_Y) >= 3) {
        Y_norm <- scale(pareto_Y)
        
        p <- plot_ly(type = 'scatterpolar', mode = 'lines')
        for(i in 1:nrow(Y_norm)) {
          p <- p %>% add_trace(r = Y_norm[i,], theta = colnames(Y_norm),
                               fill = 'toself', name = rownames(pareto_Y)[i])
        }
        p %>% layout(title = "Pareto Optimal Strategies Comparison",
                     polar = list(radialaxis = list(visible = TRUE)))
      } else {
        plotly_empty()
      }
    } else {
      plotly_empty()
    }
  })
  
  output$composite_table <- renderDT({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$pca) && !is.null(res$entropy)) {
      composite_df <- data.frame(
        strategy = rownames(res$Y),
        PC1 = res$pca$x[,1],
        PC2 = if(ncol(res$pca$x) >= 2) res$pca$x[,2] else NA,
        Entropy = res$entropy
      )
      
      datatable(composite_df, 
                options = list(pageLength = 10),
                rownames = FALSE) %>%
        formatRound(columns = c('PC1', 'PC2', 'Entropy'), digits = 3)
    }
  })
  
  output$composite_plot <- renderPlotly({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$pca) && ncol(res$pca$x) >= 2) {
      plot_data <- data.frame(
        strategy = rownames(res$Y),
        PC1 = res$pca$x[,1],
        PC2 = res$pca$x[,2],
        pareto = res$pareto_optimal
      )
      
      plot_ly(plot_data, x = ~PC1, y = ~PC2, text = ~strategy,
              type = "scatter", mode = "markers+text",
              color = ~pareto, colors = c("lightblue", "gold"),
              marker = list(size = 10),
              textposition = "top center") %>%
        layout(title = "PCA Biplot",
               xaxis = list(title = paste0("PC1 (", round(summary(res$pca)$importance[2,1]*100, 1), "%)")),
               yaxis = list(title = paste0("PC2 (", round(summary(res$pca)$importance[2,2]*100, 1), "%)")))
    } else {
      plotly_empty()
    }
  })
  
  output$composite_radar <- renderPlotly({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$pca) && nrow(res$Y) >= 3) {
      loadings <- res$pca$rotation[,1:min(3, ncol(res$pca$rotation))]
      
      plot_ly(type = 'scatterpolar', mode = 'lines') %>%
        add_trace(r = abs(loadings[,1]), theta = rownames(loadings),
                  fill = 'toself', name = 'PC1') %>%
        layout(title = "PCA Loadings",
               polar = list(radialaxis = list(visible = TRUE)))
    } else {
      plotly_empty()
    }
  })
  
  output$cluster_plot <- renderPlotly({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$Y) && nrow(res$Y) > 3 && !is.null(res$pca)) {
      set.seed(123)
      kmeans_result <- kmeans(res$Y, centers = min(input$n_clusters, nrow(res$Y) - 1))
      
      pca_scores <- res$pca$x[,1:2]
      plot_data <- data.frame(
        PC1 = pca_scores[,1],
        PC2 = pca_scores[,2],
        Cluster = as.factor(kmeans_result$cluster),
        Strategy = rownames(res$Y)
      )
      
      plot_ly(plot_data, x = ~PC1, y = ~PC2,
              color = ~Cluster, text = ~Strategy,
              type = "scatter", mode = "markers+text",
              marker = list(size = 12),
              textposition = "top center") %>%
        layout(title = "Strategy Clusters (PCA Space)",
               xaxis = list(title = "PC1"),
               yaxis = list(title = "PC2"))
    } else {
      plotly_empty()
    }
  })
  
  output$cluster_table <- renderDT({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$Y) && nrow(res$Y) > 3) {
      set.seed(123)
      kmeans_result <- kmeans(res$Y, centers = min(input$n_clusters, nrow(res$Y) - 1))
      
      cluster_df <- data.frame(
        Strategy = rownames(res$Y),
        Cluster = kmeans_result$cluster
      )
      
      datatable(cluster_df, 
                options = list(pageLength = 10),
                rownames = FALSE)
    }
  })
  
  output$summary_radar <- renderPlotly({
    req(strategy_results())
    res <- strategy_results()
    
    if(!is.null(res$Y) && ncol(res$Y) >= 3) {
      avg_values <- colMeans(res$Y, na.rm = TRUE)
      
      min_vals <- apply(res$Y, 2, min, na.rm = TRUE)
      max_vals <- apply(res$Y, 2, max, na.rm = TRUE)
      avg_norm <- (avg_values - min_vals) / (max_vals - min_vals + 1e-10)
      
      plot_ly(type = "scatterpolar",
              r = avg_norm,
              theta = names(avg_norm),
              fill = "toself",
              name = "Average") %>%
        layout(polar = list(radialaxis = list(visible = TRUE, range = c(0, 1))),
               title = "Average Performance Across Strategies")
    } else {
      plotly_empty()
    }
  })
  
  # ----------------------------------------------------------------------
  # Causal Inference Analysis
  # ----------------------------------------------------------------------
  observeEvent(input$run_causal, {
    req(processed_data(), input$treatment_var, input$causal_outcome, input$causal_covars)
    
    withProgress(message = 'Running causal analysis...', value = 0, {
      tryCatch({
        pov14 <- processed_data()
        
        incProgress(0.1, detail = "Preparing data...")
        
        complete_cases <- complete.cases(
          pov14[[input$causal_outcome]],
          pov14[[input$treatment_var]],
          pov14[, input$causal_covars, drop = FALSE]
        )
        
        if(sum(complete_cases) < ANALYSIS_CONFIG$min_observations) {
          showNotification(paste("Insufficient complete cases for analysis (need at least", 
                                 ANALYSIS_CONFIG$min_observations, ")"), type = "error")
          return()
        }
        
        pov14_complete <- pov14[complete_cases, ]
        
        Y <- pov14_complete[[input$causal_outcome]]
        W <- as.numeric(as.factor(pov14_complete[[input$treatment_var]])) - 1
        
        if(length(unique(W)) != 2) {
          showNotification("Treatment variable must have exactly 2 levels", type = "error")
          return()
        }
        
        X_df <- pov14_complete %>% select(all_of(input$causal_covars))
        X_numeric <- X_df %>%
          mutate(across(where(is.factor), as.numeric)) %>%
          mutate(across(where(is.character), as.numeric))
        X <- as.matrix(X_numeric)
        
        results <- list(
          method = input$causal_method,
          n_obs = nrow(pov14_complete),
          n_treated = sum(W == 1),
          n_control = sum(W == 0)
        )
        
        data_bal <- data.frame(W = W, X_numeric)
        
        incProgress(0.3, detail = paste("Running", input$causal_method, "..."))
        
        if(input$causal_method == "reg") {
          model_formula <- as.formula(paste("Y ~ W +", paste(colnames(X_numeric), collapse = " + ")))
          model <- lm(model_formula, data = cbind(Y = Y, W = W, X_numeric))
          
          ate <- coef(summary(model))["W", "Estimate"]
          se <- coef(summary(model))["W", "Std. Error"]
          p_value <- coef(summary(model))["W", "Pr(>|t|)"]
          
          results$ate <- data.frame(
            Estimate = ate, Std.Error = se, t.value = ate/se, p.value = p_value,
            CI.lower = ate - 1.96*se, CI.upper = ate + 1.96*se, row.names = "ATE"
          )
          results$model <- model
          results$summary <- "Regression adjustment controls linearly for covariates."
          
        } else if(input$causal_method == "ipw") {
          incProgress(0.4, detail = "Estimating propensity scores...")
          
          prop_model <- glm(W ~ ., data = data_bal, family = binomial)
          p_hat <- predict(prop_model, type = "response")
          p_hat <- pmax(p_hat, 0.05)
          p_hat <- pmin(p_hat, 0.95)
          
          weights <- ifelse(W == 1, 1/p_hat, 1/(1-p_hat))
          
          design <- svydesign(ids = ~1, weights = ~weights, data = data.frame(Y = Y, W = W))
          model <- svyglm(Y ~ W, design = design)
          
          ate <- coef(model)["W"]
          se <- sqrt(vcov(model)["W", "W"])
          p_value <- 2 * pnorm(-abs(ate/se))
          
          results$ate <- data.frame(
            Estimate = ate, Std.Error = se, t.value = ate/se, p.value = p_value,
            CI.lower = ate - 1.96*se, CI.upper = ate + 1.96*se, row.names = "ATE"
          )
          results$propensity_scores <- p_hat
          results$weights <- weights
          results$summary <- "IPW re-weights observations to balance covariates."
          
        } else if(input$causal_method == "dr") {
          incProgress(0.4, detail = "Running doubly robust estimation...")
          
          prop_model <- glm(W ~ ., data = data_bal, family = binomial)
          p_hat <- predict(prop_model, type = "response")
          p_hat <- pmax(p_hat, 0.05)
          p_hat <- pmin(p_hat, 0.95)
          
          outcome_formula <- as.formula(paste("Y ~", paste(colnames(X_numeric), collapse = " + ")))
          
          model_1 <- lm(outcome_formula, data = cbind(Y = Y, X_numeric)[W == 1, ])
          model_0 <- lm(outcome_formula, data = cbind(Y = Y, X_numeric)[W == 0, ])
          
          mu_1 <- predict(model_1, newdata = X_numeric)
          mu_0 <- predict(model_0, newdata = X_numeric)
          
          dr_score <- (W * (Y - mu_1) / p_hat + mu_1) - ((1 - W) * (Y - mu_0) / (1 - p_hat) + mu_0)
          ate <- mean(dr_score)
          se <- sd(dr_score) / sqrt(length(dr_score))
          p_value <- 2 * pnorm(-abs(ate/se))
          
          results$ate <- data.frame(
            Estimate = ate, Std.Error = se, t.value = ate/se, p.value = p_value,
            CI.lower = ate - 1.96*se, CI.upper = ate + 1.96*se, row.names = "ATE"
          )
          results$propensity_scores <- p_hat
          results$summary <- "Doubly robust combines regression and IPW for robustness."
          
        } else if(input$causal_method == "cf") {
          incProgress(0.4, detail = "Training causal forest...")
          
          cf <- causal_forest(X, Y, W, 
                              num.trees = input$cf_trees,
                              honesty = input$cf_honesty)
          
          ate_result <- average_treatment_effect(cf)
          cate <- predict(cf)$predictions
          
          results$ate <- data.frame(
            Estimate = ate_result[1], Std.Error = ate_result[2],
            t.value = ate_result[1]/ate_result[2],
            p.value = 2 * pnorm(-abs(ate_result[1]/ate_result[2])),
            CI.lower = ate_result[1] - 1.96*ate_result[2],
            CI.upper = ate_result[1] + 1.96*ate_result[2],
            row.names = "ATE"
          )
          results$cate <- cate
          results$cf_model <- cf
          results$summary <- "Causal Forest uses ML to estimate heterogeneous treatment effects."
        }
        
        incProgress(0.9, detail = "Finalizing...")
        
        causal_results(results)
        log_action("Causal Analysis", 
                   paste("Method:", input$causal_method, 
                         "- ATE:", round(results$ate$Estimate, 4)))
        showNotification("Causal analysis completed!", type = "message")
        
      }, error = function(e) {
        log_action("Causal Analysis", e$message, "error")
        showNotification(paste("Error in causal analysis:", e$message), type = "error")
      })
    })
  })
  
  # Causal outputs
  output$causal_summary <- renderPrint({
    req(causal_results())
    res <- causal_results()
    
    cat("Causal Inference Results\n")
    cat("========================\n\n")
    cat("Method:", res$method, "\n")
    cat("Total observations:", res$n_obs, "\n")
    cat("Treated:", res$n_treated, "\n")
    cat("Control:", res$n_control, "\n\n")
    cat("Summary:", res$summary, "\n")
  })
  
  output$causal_effect_plot <- renderPlotly({
    req(causal_results())
    res <- causal_results()
    
    plot_ly() %>%
      add_trace(x = res$ate$Estimate, y = "ATE",
                type = "scatter", mode = "markers",
                error_x = list(
                  type = "data",
                  symmetric = FALSE,
                  array = res$ate$CI.upper - res$ate$Estimate,
                  arrayminus = res$ate$Estimate - res$ate$CI.lower
                ),
                marker = list(size = 15, color = VIZ_CONFIG$default_colors[1])) %>%
      layout(title = "Average Treatment Effect with 95% CI",
             xaxis = list(title = "Effect Size", zeroline = TRUE),
             yaxis = list(title = ""))
  })
  
  output$balance_plot <- renderPlot({
    req(causal_results())
    res <- causal_results()
    
    tryCatch({
      if(input$causal_method == "ipw" && !is.null(res$weights)) {
        data_bal <- data.frame(
          W = rep(1:2, each = length(res$weights)/2)[1:length(res$weights)],
          weights = res$weights
        )
        love.plot(bal.tab(data_bal$W ~ ., data = data_bal, weights = res$weights),
                  threshold = 0.1, title = "Balance Diagnostics")
      } else {
        plot.new()
        text(0.5, 0.5, "Balance diagnostics available for IPW method only", cex = 1.2)
      }
    }, error = function(e) {
      plot.new()
      text(0.5, 0.5, paste("Error:", e$message), cex = 1.2)
    })
  })
  
  output$balance_table <- renderDT({
    req(causal_results())
    res <- causal_results()
    
    if(input$causal_method == "ipw") {
      datatable(data.frame(
        Variable = "Treatment",
        Mean_Treated = mean(res$n_treated/res$n_obs),
        Mean_Control = mean(res$n_control/res$n_obs),
        Std_Diff = 0
      ), options = list(dom = 't'), rownames = FALSE)
    } else {
      datatable(data.frame(Message = "Balance table available for IPW method only"), 
                options = list(dom = 't'), rownames = FALSE)
    }
  })
  
  output$ate_table <- renderDT({
    req(causal_results())
    datatable(causal_results()$ate, 
              options = list(dom = 't'),
              rownames = TRUE) %>%
      formatRound(columns = names(causal_results()$ate), digits = 4)
  })
  
  output$ate_forest_plot <- renderPlotly({
    req(causal_results())
    res <- causal_results()
    
    plot_ly() %>%
      add_trace(x = res$ate$Estimate, y = res$method,
                type = "scatter", mode = "markers",
                error_x = list(
                  type = "data",
                  symmetric = FALSE,
                  array = res$ate$CI.upper - res$ate$Estimate,
                  arrayminus = res$ate$Estimate - res$ate$CI.lower
                ),
                marker = list(size = 12, color = VIZ_CONFIG$default_colors[2])) %>%
      layout(title = "Treatment Effect Forest Plot",
             xaxis = list(title = "Effect Size"),
             yaxis = list(title = "Method"),
             shapes = list(
               list(type = "line", x0 = 0, x1 = 0, y0 = -0.5, y1 = 0.5,
                    line = list(dash = "dash", color = "red"))
             ))
  })
  
  output$cate_plot <- renderPlotly({
    req(causal_results(), input$causal_method == "cf", !is.null(causal_results()$cate))
    
    plot_ly(x = causal_results()$cate, type = "histogram",
            marker = list(color = VIZ_CONFIG$default_colors[3])) %>%
      layout(title = "Distribution of Conditional Average Treatment Effects (CATE)",
             xaxis = list(title = "CATE"),
             yaxis = list(title = "Frequency"))
  })
  
  output$cate_table <- renderDT({
    req(causal_results(), input$causal_method == "cf", !is.null(causal_results()$cate))
    
    cate_stats <- data.frame(
      Statistic = c("Mean", "SD", "Min", "25%", "Median", "75%", "Max"),
      Value = c(
        mean(causal_results()$cate, na.rm = TRUE),
        sd(causal_results()$cate, na.rm = TRUE),
        min(causal_results()$cate, na.rm = TRUE),
        quantile(causal_results()$cate, 0.25, na.rm = TRUE),
        median(causal_results()$cate, na.rm = TRUE),
        quantile(causal_results()$cate, 0.75, na.rm = TRUE),
        max(causal_results()$cate, na.rm = TRUE)
      )
    )
    
    datatable(cate_stats, 
              options = list(dom = 't'),
              rownames = FALSE) %>%
      formatRound(columns = 'Value', digits = 4)
  })
  
  output$sensitivity_plot <- renderPlotly({
    req(causal_results())
    
    plot_ly() %>%
      add_markers(x = c(-0.5, 0, 0.5), y = c("Minimal", "Selected", "All"),
                  name = "Covariate Sets",
                  marker = list(size = 12, color = VIZ_CONFIG$default_colors)) %>%
      layout(title = "Sensitivity to Covariate Selection (Illustrative)",
             xaxis = list(title = "ATE"),
             yaxis = list(title = "Model Specification"))
  })
  
  output$sensitivity_summary <- renderPrint({
    req(causal_results())
    
    cat("Sensitivity Analysis Summary\n")
    cat("===========================\n\n")
    cat("For robust causal inference, consider:\n")
    cat("1. Testing different covariate sets\n")
    cat("2. Using machine learning methods (Causal Forest)\n")
    cat("3. Checking overlap/common support\n")
    cat("4. Conducting placebo tests where possible\n")
    cat("5. Examining heterogeneity in treatment effects\n")
  })
  
  # ----------------------------------------------------------------------
  # Copula Modeling Functions (NEW)
  # ----------------------------------------------------------------------
  
  # Helper to construct formula from dropdowns
  construct_copula_formula <- function(resp, lin, sm) {
    if (is.null(resp) || resp == "" || resp == "Choose...") return("Not specified")
    lin_part <- if (length(lin) > 0) paste(lin, collapse = " + ") else NULL
    sm_part  <- if (length(sm) > 0) paste0("s(", sm, ")", collapse = " + ") else NULL
    rhs <- paste(Filter(Negate(is.null), c(lin_part, sm_part)), collapse = " + ")
    if (rhs == "") rhs <- "1"
    paste0(resp, " ~ ", rhs)
  }
  
  constructed_copula_form1 <- reactive(construct_copula_formula(input$resp1, input$preds1_lin, input$preds1_sm))
  constructed_copula_form2 <- reactive(construct_copula_formula(input$resp2, input$preds2_lin, input$preds2_sm))
  constructed_copula_form3 <- reactive(construct_copula_formula(input$resp3, input$preds3_lin, input$preds3_sm))
  
  # Final formula text (dropdown or manual)
  final_copula_form_text1 <- reactive({
    if (input$advanced_formula) {
      trimws(input$eq1_manual)
    } else {
      constructed_copula_form1()
    }
  })
  
  final_copula_form_text2 <- reactive({
    if (input$advanced_formula) {
      trimws(input$eq2_manual)
    } else {
      constructed_copula_form2()
    }
  })
  
  final_copula_form_text3 <- reactive({
    if (input$advanced_formula) {
      trimws(input$eq3_manual)
    } else {
      constructed_copula_form3()
    }
  })
  
  # Individual previews
  output$copula_form1 <- renderText({
    txt <- final_copula_form_text1()
    if (nzchar(txt) && txt != "Not specified") txt else "Not specified"
  })
  
  output$copula_form2 <- renderText({
    txt <- final_copula_form_text2()
    if (nzchar(txt) && txt != "Not specified") txt else "Not specified"
  })
  
  output$copula_form3 <- renderText({
    txt <- final_copula_form_text3()
    if (nzchar(txt) && txt != "Not specified") txt else "Not specified"
  })
  
  # Update equation choices for marginal diagnostics
  observe({
    req(input$copula_model)
    chs <- c("Equation 1" = "1", "Equation 2" = "2")
    if (input$copula_model %in% c("T", "TSS", "TESS")) {
      chs <- c(chs, "Equation 3" = "3")
    }
    updateSelectInput(session, "copula_diag_eq", choices = chs, selected = "1")
  })
  
  # Update copula pair choices
  observe({
    req(input$copula_model)
    pairs <- "1-2"
    if (input$copula_model %in% c("T", "TSS", "TESS")) {
      pairs <- c("1-2", "1-3", "2-3")
    }
    updateSelectInput(session, "copula_pair", choices = pairs, selected = pairs[1])
  })
  
  # Model fitting for copula
  observeEvent(input$run_copula, {
    req(processed_data())
    req(final_copula_form_text1(), final_copula_form_text2())
    req(nzchar(final_copula_form_text1()), nzchar(final_copula_form_text2()))
    
    withProgress(message = 'Running copula model...', value = 0, {
      tryCatch({
        d <- processed_data()
        
        incProgress(0.2, detail = "Preparing formulas...")
        
        formulas <- list(as.formula(final_copula_form_text1()), as.formula(final_copula_form_text2()))
        if (input$copula_model %in% c("T", "TSS", "TESS")) {
          req(final_copula_form_text3(), nzchar(final_copula_form_text3()))
          formulas[[3]] <- as.formula(final_copula_form_text3())
        }
        
        margins_vec <- c(input$margin1, input$margin2)
        if (input$copula_model %in% c("T", "TSS", "TESS")) {
          margins_vec <- c(margins_vec, input$margin3)
        }
        margins_vec <- margins_vec[margins_vec != "" & margins_vec != "None"]
        req(length(margins_vec) >= 2)
        
        incProgress(0.4, detail = "Setting up model parameters...")
        
        args <- list(
          formula = formulas,
          data = d,
          model = input$copula_model,
          margins = margins_vec,
          copula = input$copula_type,
          ordinal = input$ordinal,
          fp = input$fp,
          infl.fac = input$infl.fac,
          gamlssfit = input$gamlssfit,
          iterlimsp = input$iterlimsp,
          tolsp = input$tolsp,
          gc.l = input$gc.l,
          extra.regI = input$extra.regI,
          min.dn = 1e-40,
          min.pr = 1e-16,
          max.pr = 0.999999,
          drop.unused.levels = TRUE
        )
        
        if (!is.na(input$parscale) && input$parscale > 0) args$parscale <- input$parscale
        
        if (nzchar(input$knots)) {
          try(args$knots <- eval(parse(text = input$knots)), silent = TRUE)
        }
        
        if (input$copula_type == "T") args$dof <- input$dof
        
        if (input$copula_model == "ROY") {
          args$copula2 <- input$copula2
          args$dof2 <- input$dof2
        }
        
        incProgress(0.6, detail = "Fitting GJRM model...")
        
        fit <- do.call(GJRM::gjrm, args)
        
        incProgress(0.9, detail = "Finalizing...")
        
        copula_results(fit)
        log_action("Copula Model", 
                   paste("Fitted", input$copula_model, "model with", input$copula_type, "copula"))
        showNotification("Copula model fitted successfully!", type = "message")
        
      }, error = function(e) {
        log_action("Copula Model", e$message, "error")
        showNotification(paste("Error in copula model:", e$message), type = "error")
      })
    })
  })
  
  # Copula outputs
  output$copula_summary <- renderPrint({
    req(copula_results())
    summary(copula_results())
  })
  
  output$copula_conv_check <- renderPrint({
    req(copula_results())
    GJRM::conv.check(copula_results())
  })
  
  output$copula_criteria <- renderPrint({
    req(copula_results())
    fit <- copula_results()
    cat("AIC: ", round(AIC(fit), 4), "\n")
    cat("Effective degrees of freedom: ", round(fit$edf, 4), "\n")
    cat("Sample size (n): ", fit$n, "\n")
  })
  
  output$copula_assoc_params <- renderPrint({
    req(copula_results())
    fit <- copula_results()
    cat("Estimated association parameter(s):\n")
    if ("theta" %in% names(fit) && length(fit$theta) > 0) {
      print(round(fit$theta, 4))
    } else if ("theta.a" %in% names(fit)) {
      print(round(fit$theta.a, 4))
    } else {
      cat("Association parameter modeled smoothly or not directly available as constant.\n")
    }
  })
  
  output$copula_diag_plot <- renderPlot({
    req(copula_results(), input$copula_diag_eq, input$copula_diag_type)
    
    eq_num <- as.numeric(input$copula_diag_eq)
    gam_obj <- switch(eq_num,
                      "1" = copula_results()$gam1,
                      "2" = copula_results()$gam2,
                      "3" = copula_results()$gam3)
    req(gam_obj)
    
    if (input$copula_diag_type == "smooth") {
      plot(gam_obj, pages = 1, shade = TRUE, shade.col = "lightblue",
           all.terms = TRUE, scale = 0, rug = TRUE,
           main = paste("Smooth Terms - Equation", eq_num))
    } else if (input$copula_diag_type == "resfit") {
      res <- residuals(gam_obj)
      fitval <- fitted(gam_obj)
      plot(fitval, res, xlab = "Fitted Values", ylab = "Residuals",
           main = paste("Residuals vs Fitted - Equation", eq_num),
           pch = 16, col = "steelblue")
      abline(h = 0, lty = 2, col = "red", lwd = 2)
    } else if (input$copula_diag_type == "qq") {
      qqnorm(residuals(gam_obj), main = paste("Normal Q-Q Plot - Equation", eq_num))
      qqline(residuals(gam_obj), col = "red", lwd = 2)
    }
  }, height = 600)
  
  # Copula diagnostics plot
  output$copula_diag_plot2 <- renderPlot({
    req(copula_results(), input$copula_diag_type2, input$copula_pair)
    fit <- copula_results()
    d <- processed_data()
    n <- nrow(d)
    
    # Extract response variable names
    lhs_names <- sapply(fit$formula, function(f) {
      deparse(f[[2]])
    })
    
    pair <- strsplit(input$copula_pair, "-")[[1]]
    i1 <- as.numeric(pair[1])
    i2 <- as.numeric(pair[2])
    req(i1 <= length(lhs_names), i2 <= length(lhs_names))
    
    resp1_name <- lhs_names[i1]
    resp2_name <- lhs_names[i2]
    
    y1 <- d[[resp1_name]]
    y2 <- d[[resp2_name]]
    
    if (input$copula_diag_type2 == "emp_scatter") {
      u1 <- rank(y1, ties.method = "random") / (n + 1)
      u2 <- rank(y2, ties.method = "random") / (n + 1)
      
      plot(u1, u2,
           xlab = paste("Pseudo-U for Margin", i1, "(", resp1_name, ")"),
           ylab = paste("Pseudo-U for Margin", i2, "(", resp2_name, ")"),
           main = paste("Empirical Copula Scatterplot - Pair", input$copula_pair),
           pch = 21, bg = adjustcolor("darkblue", alpha.f = 0.6), col = adjustcolor("blue", alpha.f = 0.8),
           cex = 1.2)
      grid(lty = 2, col = "gray")
      abline(0, 1, col = "red", lwd = 2, lty = 2)
      text(0.02, 0.98, paste("Copula:", input$copula_type), adj = c(0, 1), cex = 1.1, col = "darkgreen")
    } else if (input$copula_diag_type2 == "theta_smooth") {
      # Find indices of theta equations
      theta_idx <- which(grepl("^theta", lhs_names))
      if (length(theta_idx) == 0) {
        plot(1, type = "n", axes = FALSE, xlab = "", ylab = "")
        text(1, 1, "No smooth term for dependence parameter (constant association).", cex = 1.5)
        return()
      }
      gam_theta <- fit[[paste0("gam", theta_idx[1])]]
      req(gam_theta)
      plot(gam_theta, pages = 1, shade = TRUE, shade.col = "orange",
           rug = TRUE, scale = 0,
           main = "Smooth Term for Dependence Parameter (theta)")
    }
  }, height = 600)
  
  output$copula_diag_note <- renderText({
    if (input$copula_diag_type2 == "emp_scatter") {
      "Note: Points near the main diagonal indicate positive dependence. Clustering in corners suggests tail dependence. For independence, points should fill the unit square uniformly. Ties (discrete/binary margins) appear as horizontal/vertical lines."
    } else {
      ""
    }
  })
  
  output$download_copula_fit <- downloadHandler(
    filename = function() { "gjrm_copula_fit.rds" },
    content = function(file) {
      req(copula_results())
      saveRDS(copula_results(), file)
    }
  )
  
  # ----------------------------------------------------------------------
  # Analysis Log Tab Outputs
  # ----------------------------------------------------------------------
  output$activity_log_table <- renderDT({
    datatable(analysis_log(),
              options = list(pageLength = 25, order = list(list(0, 'desc'))),
              filter = 'top',
              rownames = FALSE) %>%
      formatStyle('status',
                  backgroundColor = styleEqual(
                    c('success', 'error', 'warning', 'info'),
                    c('lightgreen', 'lightcoral', 'lightyellow', 'lightblue')
                  ))
  })
  
  output$session_stats <- renderPrint({
    cat("Session Statistics\n")
    cat("==================\n\n")
    cat("Session started:", format(session_start, "%Y-%m-%d %H:%M:%S"), "\n")
    cat("Session duration:", round(difftime(Sys.time(), session_start, units = "mins"), 1), "minutes\n")
    cat("Total actions:", nrow(analysis_log()), "\n")
    cat("Successful actions:", sum(analysis_log()$status == "success"), "\n")
    cat("Errors:", sum(analysis_log()$status == "error"), "\n")
    cat("Cache hits:", cache_hits(), "\n")
  })
  
  output$cache_info <- renderPrint({
    cache_dir <- CACHE_CONFIG$directory
    
    cat("Cache Information\n")
    cat("=================\n\n")
    cat("Cache enabled:", CACHE_CONFIG$enabled, "\n")
    cat("Cache directory:", cache_dir, "\n")
    
    if(dir.exists(cache_dir)) {
      files <- list.files(cache_dir)
      cat("Cached files:", length(files), "\n")
      
      if(length(files) > 0) {
        total_size <- sum(file.info(file.path(cache_dir, files))$size)
        cat("Total cache size:", round(total_size / 1024^2, 2), "MB\n")
      }
    } else {
      cat("Cache directory does not exist\n")
    }
  })
  
  observeEvent(input$clear_log, {
    analysis_log(data.frame(
      timestamp = character(),
      action = character(),
      details = character(),
      status = character(),
      stringsAsFactors = FALSE
    ))
    showNotification("Analysis log cleared", type = "message")
  })
  
  observeEvent(input$clear_cache, {
    if(dir.exists(CACHE_CONFIG$directory)) {
      unlink(file.path(CACHE_CONFIG$directory, "*"))
      showNotification("Cache cleared", type = "message")
    }
  })
  
  observeEvent(input$refresh_log, {
    showNotification("Log refreshed", type = "message")
  })
  
  # ----------------------------------------------------------------------
  # Download Handlers
  # ----------------------------------------------------------------------
  output$download_processed_csv <- downloadHandler(
    filename = function() paste0("processed_data_", Sys.Date(), ".csv"),
    content = function(file) {
      df <- processed_data()
      if(is.null(df)) {
        showNotification("No data to export", type = "error")
        return()
      }
      write.csv(df, file, row.names = FALSE)
    }
  )
  
  output$download_processed_rda <- downloadHandler(
    filename = function() paste0("processed_data_", Sys.Date(), ".rds"),
    content = function(file) {
      df <- processed_data()
      if(is.null(df)) {
        showNotification("No data to export", type = "error")
        return()
      }
      saveRDS(df, file)
    }
  )
  
  output$download_processed_stata <- downloadHandler(
    filename = function() paste0("processed_data_", Sys.Date(), ".dta"),
    content = function(file) {
      df <- processed_data()
      if(is.null(df)) {
        showNotification("No data to export", type = "error")
        return()
      }
      tryCatch({
        haven::write_dta(df, file)
      }, error = function(e) {
        write.csv(df, file, row.names = FALSE)
      })
    }
  )
  
  output$download_codebook <- downloadHandler(
    filename = function() paste0("codebook_", Sys.Date(), ".pdf"),
    content = function(file) {
      df <- processed_data()
      if(is.null(df)) {
        showNotification("No data to export", type = "error")
        return()
      }
      
      pdf(file, width = 10, height = 7)
      plot.new()
      title <- paste("Data Codebook - Generated", Sys.Date())
      text(0.5, 0.9, title, cex = 1.5)
      
      var_info <- data.frame(
        Variable = names(df),
        Type = sapply(df, function(x) class(x)[1]),
        Missing = colSums(is.na(df)),
        Unique = sapply(df, function(x) length(unique(na.omit(x))))
      )
      
      grid.newpage()
      grid.table(head(var_info, 30))
      dev.off()
    }
  )
  
  output$download_aggregated <- downloadHandler(
    filename = function() paste0("country_aggregates_", Sys.Date(), ".csv"),
    content = function(file) {
      df <- aggregated_data()
      if(is.null(df)) {
        showNotification("No aggregated data to export", type = "error")
        return()
      }
      write.csv(df, file, row.names = FALSE)
    }
  )
  
  output$download_strategy <- downloadHandler(
    filename = function() paste0("strategy_results_", Sys.Date(), ".zip"),
    content = function(file) {
      tmpdir <- tempdir()
      files <- c()
      
      if(!is.null(strategy_results())) {
        saveRDS(strategy_results(), file.path(tmpdir, "strategy_results.rds"))
        files <- c(files, file.path(tmpdir, "strategy_results.rds"))
        
        write.csv(strategy_results()$agg, file.path(tmpdir, "strategy_aggregates.csv"), row.names = FALSE)
        files <- c(files, file.path(tmpdir, "strategy_aggregates.csv"))
      }
      
      if(length(files) == 0) {
        showNotification("No strategy results to export", type = "error")
        return()
      }
      
      zip(file, files = files, flags = "-j")
    }
  )
  
  output$download_causal <- downloadHandler(
    filename = function() paste0("causal_results_", Sys.Date(), ".zip"),
    content = function(file) {
      tmpdir <- tempdir()
      files <- c()
      
      if(!is.null(causal_results())) {
        saveRDS(causal_results(), file.path(tmpdir, "causal_results.rds"))
        files <- c(files, file.path(tmpdir, "causal_results.rds"))
        
        write.csv(causal_results()$ate, file.path(tmpdir, "causal_ate.csv"), row.names = TRUE)
        files <- c(files, file.path(tmpdir, "causal_ate.csv"))
      }
      
      if(length(files) == 0) {
        showNotification("No causal results to export", type = "error")
        return()
      }
      
      zip(file, files = files, flags = "-j")
    }
  )
  
  output$download_copula_results <- downloadHandler(
    filename = function() paste0("copula_results_", Sys.Date(), ".zip"),
    content = function(file) {
      tmpdir <- tempdir()
      files <- c()
      
      if(!is.null(copula_results())) {
        saveRDS(copula_results(), file.path(tmpdir, "copula_results.rds"))
        files <- c(files, file.path(tmpdir, "copula_results.rds"))
        
        summary_text <- capture.output(summary(copula_results()))
        writeLines(summary_text, file.path(tmpdir, "copula_summary.txt"))
        files <- c(files, file.path(tmpdir, "copula_summary.txt"))
      }
      
      if(length(files) == 0) {
        showNotification("No copula results to export", type = "error")
        return()
      }
      
      zip(file, files = files, flags = "-j")
    }
  )
  
  output$download_all <- downloadHandler(
    filename = function() paste0("strategy_analytics_export_", Sys.Date(), ".zip"),
    content = function(file) {
      tmpdir <- tempdir()
      files <- c()
      
      if(!is.null(processed_data())) {
        csv_file <- file.path(tmpdir, "processed_data.csv")
        write.csv(processed_data(), csv_file, row.names = FALSE)
        files <- c(files, csv_file)
      }
      
      if(!is.null(aggregated_data())) {
        agg_file <- file.path(tmpdir, "aggregated_data.csv")
        write.csv(aggregated_data(), agg_file, row.names = FALSE)
        files <- c(files, agg_file)
      }
      
      if(!is.null(strategy_results())) {
        strat_file <- file.path(tmpdir, "strategy_results.rds")
        saveRDS(strategy_results(), strat_file)
        files <- c(files, strat_file)
      }
      
      if(!is.null(causal_results())) {
        causal_file <- file.path(tmpdir, "causal_results.rds")
        saveRDS(causal_results(), causal_file)
        files <- c(files, causal_file)
      }
      
      if(!is.null(copula_results())) {
        copula_file <- file.path(tmpdir, "copula_results.rds")
        saveRDS(copula_results(), copula_file)
        files <- c(files, copula_file)
      }
      
      log_file <- file.path(tmpdir, "analysis_log.csv")
      write.csv(analysis_log(), log_file, row.names = FALSE)
      files <- c(files, log_file)
      
      if(length(files) == 0) {
        showNotification("No data to export", type = "error")
        return()
      }
      
      zip(file, files = files, flags = "-j")
    }
  )
  
  output$export_log <- downloadHandler(
    filename = function() paste0("analysis_log_", Sys.Date(), ".csv"),
    content = function(file) {
      log <- analysis_log()
      if(nrow(log) == 0) {
        showNotification("No log entries to export", type = "error")
        return()
      }
      write.csv(log, file, row.names = FALSE)
    }
  )
  
  observeEvent(input$generate_report, {
    showNotification("R Markdown report generation would create comprehensive HTML/PDF report with all analyses", 
                     type = "info", duration = 7)
  })
  
  # Session cleanup
  session$onSessionEnded(function() {
    if(CACHE_CONFIG$auto_clean) {
      tryCatch({
        clean_temp_files(CACHE_CONFIG$directory, CACHE_CONFIG$max_age_hours)
      }, error = function(e) {
        message("Session cleanup error: ", e$message)
      })
    }
  })
}

# ==============================================================================
# Run the App
# ==============================================================================
shinyApp(ui = ui, server = server)
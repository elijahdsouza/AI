@echo off
title UC Pro Group
cd /d "%~dp0"

where node >nul 2>nul
if errorlevel 1 (
  echo.
  echo   Node.js isn't installed yet.
  echo   1. Install the LTS version from nodejs.org. The page is opening now.
  echo   2. Then double-click start-windows.bat again.
  echo.
  start "" "https://nodejs.org/en/download"
  pause
  exit /b 1
)

if not exist node_modules (
  echo.
  echo   First run: installing. This takes a minute or two...
  echo.
  call npm install
  if errorlevel 1 (
    echo.
    echo   The install didn't finish. Scroll up for the reason.
    pause
    exit /b 1
  )
)

echo.
echo   Starting the site. Your browser will open at http://localhost:5173
echo   Keep this window open while you use it. Close it to stop the site.
echo.
call npm run dev -- --open
pause

#!/bin/bash
# Double-click to run the site. The first time, macOS may ask: right-click, then Open.
cd "$(dirname "$0")" || exit 1

if ! command -v node >/dev/null 2>&1; then
  echo "Node.js isn't installed yet. Install the LTS version from nodejs.org (opening it now), then open this file again."
  open "https://nodejs.org/en/download"
  read -r -p "Press Return to close."
  exit 1
fi

if [ ! -d node_modules ]; then
  echo "First run: installing. This takes a minute or two..."
  npm install || { read -r -p "The install didn't finish. Scroll up for the reason. Press Return to close."; exit 1; }
fi

echo "Starting the site. Your browser will open at http://localhost:5173"
echo "Keep this window open while you use it. Close it to stop the site."
npm run dev -- --open

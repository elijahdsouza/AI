import { StrictMode } from 'react'
import { createRoot } from 'react-dom/client'
import './index.css'
import App from './App.tsx'

function mount(el: HTMLElement) {
  createRoot(el).render(
    <StrictMode>
      <App />
    </StrictMode>,
  )
}

// Some file previewers run the one-file build's script before they add the page
// body. If #root isn't there yet, wait for it instead of failing on a blank page.
const root = document.getElementById('root')
if (root) mount(root)
else {
  const watch = new MutationObserver(() => {
    const el = document.getElementById('root')
    if (el) { watch.disconnect(); mount(el) }
  })
  watch.observe(document.documentElement, { childList: true, subtree: true })
}

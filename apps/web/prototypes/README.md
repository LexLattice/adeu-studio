# Morphic Surface Prototype Notes

This folder holds app-adjacent prototype surfaces that may be wired into the
`apps/web` Next route tree once their runtime stack is present.

`adeu-studio-morphic-surface.jsx` currently assumes:

- `framer-motion`
- `three`
- `@react-three/fiber`
- `@react-three/drei`

It also relies heavily on Tailwind-style utility classes. `apps/web` now ships
Tailwind v4 via `src/app/globals.css` + `postcss.config.mjs`, and the prototype
is exposed at `/morphic-studio`.

The concept is morphic-UX aligned at the scene/theory level, but it is not yet
repo-native in the stronger ADEU sense because it is hand-authored visual code,
not a surface compiled from typed `ux_morph_ir` / `ux_surface_projection`
artifacts.

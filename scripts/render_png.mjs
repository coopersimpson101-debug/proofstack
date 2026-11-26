// Render an SVG to PNG with resvg (npm i @resvg/resvg-js).
//   node scripts/render_png.mjs docs/assets/banner.svg docs/assets/banner.png 1280
import { readFileSync, writeFileSync } from "node:fs";
import { createRequire } from "node:module";

const require = createRequire(process.env.RESVG_FROM || import.meta.url);
const { Resvg } = require("@resvg/resvg-js");
const [src, dst, width] = process.argv.slice(2);
const r = new Resvg(readFileSync(src, "utf8"), {
  fitTo: { mode: "width", value: Number(width || 1280) },
  font: { loadSystemFonts: true },
});
writeFileSync(dst, r.render().asPng());
console.log(`wrote ${dst}`);

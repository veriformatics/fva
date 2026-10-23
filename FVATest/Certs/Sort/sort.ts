import { readFileSync } from "node:fs";

const xs: number[] = readFileSync(0, "utf8")
  .split("\n")
  .filter((line) => line !== "")
  .map(Number);
xs.sort((a, b) => a - b);
process.stdout.write(xs.map((x) => `${x}\n`).join(""));

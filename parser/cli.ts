// CLI: check a surface-syntax file with the kernel.
//
//   deno run --allow-read parser/cli.ts <file>
//
// Prints each `#check` result, then a confirmation, or a positioned error.

import { DriverError, runModule } from "./driver.ts";
import { ParseError } from "./syntax.ts";

async function main(): Promise<void> {
  const file = Deno.args[0];
  if (file === undefined) {
    console.error("usage: cli <file>");
    Deno.exit(2);
  }

  const src = await Deno.readTextFile(file);
  try {
    const { checks } = runModule(src);
    for (const c of checks) console.log(c.text);
    console.log(`✓ ${file}: all declarations accepted`);
  } catch (e) {
    if (e instanceof ParseError || e instanceof DriverError) {
      console.error(`${file}:${e.message}`);
      Deno.exit(1);
    }
    throw e;
  }
}

if (import.meta.main) await main();

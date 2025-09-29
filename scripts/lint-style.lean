/-
Copyright (c) 2025 ModalDistribution Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

open System

partial def findLeanFiles (dir : FilePath) : IO (Array FilePath) := do
  let mut result := #[]
  if ← dir.isDir then
    for entry in ← dir.readDir do
      if entry.fileName.endsWith ".lean" then
        result := result.push entry.path
      else if ← entry.path.isDir then
        -- Skip hidden directories and build directories
        if !entry.fileName.startsWith "." && entry.fileName != ".lake" && entry.fileName != "build" then
          result := result ++ (← findLeanFiles entry.path)
  return result

def main (_ : List String) : IO UInt32 := do
  let mut errors := 0

  -- Find all .lean files in the project
  let leanFiles ← findLeanFiles (FilePath.mk "ModalDistribution")

  for file in leanFiles do
    let contents ← IO.FS.readFile file
    let lines := contents.splitOn "\n"

    -- Check for various style issues
    for h : i in [:lines.length] do
      let line := lines[i]
      let lineNum := i + 1

      -- Check for trailing whitespace
      if line.trimRight != line then
        IO.println s!"{file}:{lineNum}: Trailing whitespace found"
        errors := errors + 1

      -- Check for tabs (should use spaces)
      if line.contains '\t' then
        IO.println s!"{file}:{lineNum}: Tab character found (use spaces instead)"
        errors := errors + 1

      -- Check line length (warn if > 100 chars, error if > 120)
      if line.length > 120 then
        IO.println s!"{file}:{lineNum}: Line too long ({line.length} > 120 characters)"
        errors := errors + 1
      else if line.length > 100 then
        IO.println s!"{file}:{lineNum}: Warning: Line is long ({line.length} > 100 characters)"

      -- Check for multiple consecutive blank lines
      if i > 0 && line.isEmpty && lines[i-1]!.isEmpty then
        IO.println s!"{file}:{lineNum}: Multiple consecutive blank lines"
        errors := errors + 1

    -- Check file ends with newline
    if !contents.isEmpty && !contents.endsWith "\n" then
      IO.println s!"{file}: File does not end with a newline"
      errors := errors + 1

  if errors > 0 then
    IO.println s!"\nFound {errors} style error(s)"
    return 1
  else
    IO.println "All style checks passed!"
    return 0
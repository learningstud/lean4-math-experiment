def main : IO Unit := do
  let stdout ← IO.getStdout
  stdout.putStrLn s!"Imagine that programs ran like Kipchoge!"

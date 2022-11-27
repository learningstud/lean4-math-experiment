import Geometry

def main : IO Unit := do
  let stdout ← IO.getStdout
  let book := Hartshorne2000
  stdout.putStrLn s!"{book.author} {book.year} - {book.title}"
  stdout.putStrLn s!"ISBN: {book.isbn}"

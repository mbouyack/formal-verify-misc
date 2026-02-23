import FormalVerifyMisc.CodeChef.Template.Primes

def main : List String → IO UInt32 := fun _ => do
  let result := CodeChef.primes.size
  IO.println s!"Result: {result}"
  --IO.println s!"Hello, world!"
  return 0

import LeanMumu.Basic

namespace Core

abbrev ParseM := StateT (List Char) (Except String)

def isSpace (c : Char) : Bool :=
  c = ' ' || c = '\n' || c = '\t' || c = '\r'

def startsWith (pfx xs : List Char) : Bool :=
  pfx == xs.take pfx.length

def skipWs : ParseM Unit := do
  modify (List.dropWhile isSpace)

def peekNonWs : ParseM (Option Char) := do
  skipWs
  match (← get) with
  | c :: _ => pure (some c)
  | [] => pure none

def peekNextNonWs : ParseM (Option Char) := do
  skipWs
  match (← get) with
  | _ :: c :: _ => pure (some c)
  | _ => pure none

def expectChar (c : Char) : ParseM Unit := do
  skipWs
  match (← get) with
  | d :: ds =>
      if d = c then
        set ds
      else
        throw s!"expected '{c}'"
  | [] => throw s!"expected '{c}'"

def tryConsumeChar (c : Char) : ParseM Bool := do
  skipWs
  match (← get) with
  | d :: ds =>
      if d = c then
        set ds
        pure true
      else
        pure false
  | [] => pure false

def tryConsumeStr (s : String) : ParseM Bool := do
  skipWs
  let pfx := s.toList
  let rest := (← get)
  if startsWith pfx rest then
    set (rest.drop pfx.length)
    pure true
  else
    pure false

def splitWhile (p : Char -> Bool) : List Char -> List Char × List Char
  | [] => ([], [])
  | c :: cs =>
      if p c then
        let (a, b) := splitWhile p cs
        (c :: a, b)
      else
        ([], c :: cs)

def parseNat : ParseM Nat := do
  skipWs
  let st := (← get)
  let (digits, rest) := splitWhile (fun c => c.isDigit) st
  if digits.isEmpty then
    throw "expected natural number"
  set rest
  match (String.ofList digits).toNat? with
  | some n => pure n
  | none => throw "invalid natural number"

def parseInt : ParseM Int := do
  skipWs
  let neg ← tryConsumeChar '-'
  let n ← parseNat
  if neg then
    pure (Int.negOfNat n)
  else
    pure (Int.ofNat n)

def parseVar : ParseM Var := do
  if (← tryConsumeStr "x_") then
    parseNat
  else
    throw "expected variable x_<n>"

def parseCoVar : ParseM CoVar := do
  if (← tryConsumeStr "a_") then
    parseNat
  else
    throw "expected covariable a_<n>"

def parseOp : ParseM Op := do
  if (← tryConsumeChar '+') then
    pure .add
  else if (← tryConsumeChar '*') then
    pure .mul
  else if (← tryConsumeChar '-') then
    pure .sub
  else if (← tryConsumeStr "add") then
    pure .add
  else if (← tryConsumeStr "mul") then
    pure .mul
  else if (← tryConsumeStr "sub") then
    pure .sub
  else
    throw "expected operator (+, *, -, add, mul, sub)"

mutual
  partial def parseProducer : ParseM Producer := do
    if (← tryConsumeChar 'μ') || (← tryConsumeStr "mu") then
      let a ← parseCoVar
      expectChar '.'
      let s ← parseStatement
      pure (.mu a s)
    else if (← tryConsumeChar '⌜') then
      let n ← parseInt
      expectChar '⌝'
      pure (.lit n)
    else if (← tryConsumeStr "lit") then
      let n ← parseInt
      pure (.lit n)
    else if (← tryConsumeStr "x_") then
      let n ← parseNat
      pure (.var n)
    else
      let c? ← peekNonWs
      let c2? ← peekNextNonWs
      match c?, c2? with
      | some c, _ =>
          if c.isDigit then
            let n ← parseInt
            pure (.lit n)
          else if c = '-' && c2?.map Char.isDigit = some true then
            let n ← parseInt
            pure (.lit n)
          else
            throw "expected producer"
      | none, _ => throw "expected producer"

  partial def parseConsumer : ParseM Consumer := do
    let a ← parseCoVar
    pure (.covar a)

  partial def parseStatement : ParseM Statement := do
    if (← tryConsumeChar '⟨') then
      let p ← parseProducer
      expectChar '|'
      let c ← parseConsumer
      expectChar '⟩'
      pure (.cut p c)
    else if (← tryConsumeChar '<') then
      let p ← parseProducer
      expectChar '|'
      let c ← parseConsumer
      expectChar '>'
      pure (.cut p c)
    else if (← tryConsumeStr "cut(") then
      let p ← parseProducer
      expectChar ','
      let c ← parseConsumer
      expectChar ')'
      pure (.cut p c)
    else if (← tryConsumeStr "ifz(") then
      let p ← parseProducer
      expectChar ','
      let s1 ← parseStatement
      expectChar ','
      let s2 ← parseStatement
      expectChar ')'
      pure (.ifz p s1 s2)
    else if (← tryConsumeStr "prim(") then
      let op ← parseOp
      expectChar ','
      let p1 ← parseProducer
      expectChar ','
      let p2 ← parseProducer
      expectChar ';'
      let c ← parseConsumer
      expectChar ')'
      pure (.prim op p1 p2 c)
    else
      -- operator form like +(p1, p2; c)
      let op ← parseOp
      expectChar '('
      let p1 ← parseProducer
      expectChar ','
      let p2 ← parseProducer
      expectChar ';'
      let c ← parseConsumer
      expectChar ')'
      pure (.prim op p1 p2 c)
end

def parseStatementFromString (s : String) : Except String Statement := do
  let (st, rest) ← (parseStatement).run s.toList
  let rest' := rest.dropWhile isSpace
  if rest'.isEmpty then
    pure st
  else
    throw s!"unexpected input: {String.ofList rest'}"

end Core

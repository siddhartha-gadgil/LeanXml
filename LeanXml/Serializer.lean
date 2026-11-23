/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanXml.Basic

/-!
# Serializing an `Element` to well-formed XML 1.0

`Element.toXml` writes an `Element` as XML text in which character data and attribute values
are escaped. It returns an error, never ill-formed text, for a tree that XML 1.0 cannot
represent: a name that is not a `Name`, a character outside `Char`, or a comment that
contains `--`, ends with `-` or holds a carriage return.

The `ToString` instances of `LeanXml.Basic` are unchanged: they still print text and
attribute values verbatim.
-/

namespace Lean
namespace Xml

/-- https://www.w3.org/TR/xml/#NT-Char -/
def isChar (c : Char) : Bool :=
  let n := c.toNat
  n = 0x9 || n = 0xA || n = 0xD
    || (0x20 ≤ n && n ≤ 0xD7FF) || (0xE000 ≤ n && n ≤ 0xFFFD) || (0x10000 ≤ n && n ≤ 0x10FFFF)

/-- https://www.w3.org/TR/xml/#NT-NameStartChar -/
def isNameStartChar (c : Char) : Bool :=
  let n := c.toNat
  c = ':' || c = '_' || ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z')
    || (0xC0 ≤ n && n ≤ 0xD6) || (0xD8 ≤ n && n ≤ 0xF6) || (0xF8 ≤ n && n ≤ 0x2FF)
    || (0x370 ≤ n && n ≤ 0x37D) || (0x37F ≤ n && n ≤ 0x1FFF) || (0x200C ≤ n && n ≤ 0x200D)
    || (0x2070 ≤ n && n ≤ 0x218F) || (0x2C00 ≤ n && n ≤ 0x2FEF) || (0x3001 ≤ n && n ≤ 0xD7FF)
    || (0xF900 ≤ n && n ≤ 0xFDCF) || (0xFDF0 ≤ n && n ≤ 0xFFFD) || (0x10000 ≤ n && n ≤ 0xEFFFF)

/-- https://www.w3.org/TR/xml/#NT-NameChar -/
def isNameChar (c : Char) : Bool :=
  let n := c.toNat
  isNameStartChar c || c = '-' || c = '.' || ('0' ≤ c && c ≤ '9') || n = 0xB7
    || (0x300 ≤ n && n ≤ 0x36F) || (0x203F ≤ n && n ≤ 0x2040)

/-- https://www.w3.org/TR/xml/#NT-Name -/
def isName (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: cs => isNameStartChar c && cs.all isNameChar

/-- Why an `Element` has no XML 1.0 serialization. -/
inductive SerializeError
  /-- An element or attribute name that is not an XML `Name`. -/
  | invalidName (name : String)
  /-- A character outside the XML `Char` production; no character reference may name it. -/
  | invalidChar (c : Char) (text : String)
  /-- A comment that contains `--`, ends with `-`, or holds a carriage return, which a parser
  would normalize to a line feed and a comment has no way to escape. -/
  | invalidComment (comment : String)
deriving BEq, DecidableEq, Repr, Inhabited

instance : ToString SerializeError where
  toString
    | .invalidName n => s!"not an XML name: {n.quote}"
    | .invalidChar c t => s!"character U+{(String.ofList (Nat.toDigits 16 c.toNat)).toUpper} in {t.quote} is not an XML character"
    | .invalidComment c => s!"an XML comment cannot contain \"--\" or a carriage return, or end with \"-\": {c.quote}"

private def checkChars (s : String) : Except SerializeError Unit :=
  match s.toList.find? (!isChar ·) with
  | some c => throw (.invalidChar c s)
  | none => pure ()

private def checkName (s : String) : Except SerializeError Unit :=
  if isName s then pure () else throw (.invalidName s)

/-- Escapes character data: `&`, `<`, `>`, and carriage return, which a parser would
otherwise normalize to a line feed. -/
def escapeText (s : String) : Except SerializeError String := do
  checkChars s
  return s.foldl (init := "") fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '\r' => acc ++ "&#xD;"
    | c => acc.push c

/-- Escapes an attribute value for double quotes: `&`, `<`, `>`, `"`, and tab, line feed and
carriage return, which a parser would otherwise normalize to spaces. -/
def escapeAttrValue (s : String) : Except SerializeError String := do
  checkChars s
  return s.foldl (init := "") fun acc c =>
    match c with
    | '&' => acc ++ "&amp;"
    | '<' => acc ++ "&lt;"
    | '>' => acc ++ "&gt;"
    | '"' => acc ++ "&quot;"
    | '\t' => acc ++ "&#x9;"
    | '\n' => acc ++ "&#xA;"
    | '\r' => acc ++ "&#xD;"
    | c => acc.push c

private def commentToXml (c : String) : Except SerializeError String := do
  checkChars c
  if (c.splitOn "--").length > 1 || c.endsWith "-" || c.contains (· == '\r') then throw (.invalidComment c)
  return s!"<!--{c}-->"

private def attributesToXml (as : Attributes) : Except SerializeError String :=
  as.foldlM (init := "") fun acc n v => do
    checkName n
    return acc ++ s!" {n}=\"{← escapeAttrValue v}\""

mutual
/-- The element as XML text, with `<name/>` for an element without content. -/
def Element.toXml : Xml.Element → Except SerializeError String
  | .Element n a c => do
    checkName n
    let as ← attributesToXml a
    let cs ← c.mapM Content.toXml
    if cs.all (· == "") then return s!"<{n}{as}/>"
    return s!"<{n}{as}>{String.join cs.toList}</{n}>"

/-- The content item as XML text. -/
def Content.toXml : Content → Except SerializeError String
  | .Element e => e.toXml
  | .Comment c => commentToXml c
  | .Character c => escapeText c
end

/-- The element as an XML document: an XML declaration, then the element. -/
def Element.toXmlDocument (e : Xml.Element) : Except SerializeError String :=
  return "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n" ++ (← e.toXml) ++ "\n"

private def joinText (cs : Array Content) : Array Content :=
  cs.foldl (init := #[]) fun acc c =>
    match acc.back?, c with
    | _, .Character "" => acc
    | some (.Character x), .Character y => acc.pop.push (.Character (x ++ y))
    | _, c => acc.push c

mutual
/-- The tree that parsing `e.toXml` yields: empty character data is dropped and adjacent
character data is joined, at every level. -/
def Element.normalize : Xml.Element → Xml.Element
  | .Element n a c => .Element n a (joinText (c.map Content.normalize))

/-- Normalizes the element inside a content item. -/
def Content.normalize : Content → Content
  | .Element e => .Element e.normalize
  | c => c
end

end Xml
end Lean

import LeanXml

/-! Tests of `Element.toXml`: what is escaped, what is refused, and that `parse` reads the
serialization back to the same tree. Each `#guard` is checked when this module is built. -/

namespace LeanXmlTest
open Lean Xml

mutual
def elementEq : Element → Element → Bool
  | .Element n a c, .Element n' a' c' =>
    n == n' && a.toList == a'.toList && c.size == c'.size
      && (c.attach.zip c').all fun (⟨x, _⟩, y) => contentEq x y

def contentEq : Content → Content → Bool
  | .Element e, .Element e' => elementEq e e'
  | .Comment c, .Comment c' => c == c'
  | .Character c, .Character c' => c == c'
  | _, _ => false
end

instance : BEq Element := ⟨elementEq⟩

def elem (name : String) (attrs : List (String × String) := []) (content : Array Content := #[]) :
    Element :=
  .Element name (Std.TreeMap.ofList attrs compare) content

def text (s : String) : Element := elem "a" [] #[.Character s]
def attr (s : String) : Element := elem "a" [("v", s)]

def xml (e : Element) : Option String := e.toXml.toOption
def err (e : Element) : Option SerializeError :=
  match e.toXml with
  | .ok _ => none
  | .error x => some x

/-- `parse` reads `e.toXml` back to `e`. -/
def roundTrips (e : Element) : Bool :=
  match e.toXml with
  | .ok s => match parse s with
    | .ok e' => e' == e
    | .error _ => false
  | .error _ => false

/-- `parse` reads `e.toXml` back to `e.normalize`. -/
def roundTripsToNormal (e : Element) : Bool :=
  match e.toXml with
  | .ok s => match parse s with
    | .ok e' => e' == e.normalize
    | .error _ => false
  | .error _ => false

/-! ## Character data -/

#guard xml (text "a & b") == some "<a>a &amp; b</a>"
#guard xml (text "1 < 2") == some "<a>1 &lt; 2</a>"
#guard xml (text "2 > 1") == some "<a>2 &gt; 1</a>"
#guard xml (text "x]]>y") == some "<a>x]]&gt;y</a>"
#guard xml (text "&amp;") == some "<a>&amp;amp;</a>"
#guard xml (text "line\r\nnext") == some "<a>line&#xD;\nnext</a>"
#guard xml (text "\"quoted\" 'too'\ttab") == some "<a>\"quoted\" 'too'\ttab</a>"
#guard xml (text "é 語 𝔘") == some "<a>é 語 𝔘</a>"

/-! ## Attribute values -/

#guard xml (attr "a & b") == some "<a v=\"a &amp; b\"/>"
#guard xml (attr "1 < 2") == some "<a v=\"1 &lt; 2\"/>"
#guard xml (attr "2 > 1") == some "<a v=\"2 &gt; 1\"/>"
#guard xml (attr "say \"hi\"") == some "<a v=\"say &quot;hi&quot;\"/>"
#guard xml (attr "it's") == some "<a v=\"it's\"/>"
#guard xml (attr "a\tb\nc\rd") == some "<a v=\"a&#x9;b&#xA;c&#xD;d\"/>"

/-! ## Elements, comments and the document form -/

#guard xml (elem "a") == some "<a/>"
#guard xml (elem "a" [] #[.Character ""]) == some "<a/>"
#guard xml (elem "a" [("y", "2"), ("x", "1")] #[.Element (elem "b"), .Comment " c & <d> "])
  == some "<a x=\"1\" y=\"2\"><b/><!-- c & <d> --></a>"
#guard (elem "a").toXmlDocument.toOption == some "<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n<a/>\n"

/-! ## What cannot be represented is an error -/

#guard err (elem "a" [] #[.Comment "a--b"]) == some (.invalidComment "a--b")
#guard err (elem "a" [] #[.Comment "ab-"]) == some (.invalidComment "ab-")
#guard err (elem "a" [] #[.Comment "a\r\nb"]) == some (.invalidComment "a\r\nb")
#guard err (elem "a" [] #[.Comment "-a-b"]) == none
#guard err (text "a\x00b") == some (.invalidChar '\x00' "a\x00b")
#guard err (text "bell\x07") == some (.invalidChar '\x07' "bell\x07")
#guard err (text "\uFFFE") == some (.invalidChar '\uFFFE' "\uFFFE")
#guard err (attr "\x1B[0m") == some (.invalidChar '\x1B' "\x1B[0m")
#guard err (elem "a" [] #[.Comment "\x0C"]) == some (.invalidChar '\x0C' "\x0C")
#guard err (elem "") == some (.invalidName "")
#guard err (elem "1a") == some (.invalidName "1a")
#guard err (elem "a b") == some (.invalidName "a b")
#guard err (elem "a>") == some (.invalidName "a>")
#guard err (elem "a" [("x y", "1")]) == some (.invalidName "x y")
#guard err (elem "a" [] #[.Element (elem "-b")]) == some (.invalidName "-b")
#guard err (elem "xml:lang-é_1.x") == none
#guard toString (SerializeError.invalidChar '\x07' "a\x07") ==
  "character U+7 in \"a\\x07\" is not an XML character"

/-! ## Parsing the serialization returns the tree -/

/-- Every string of at most `n` characters drawn from `alphabet`. -/
def strings (alphabet : List Char) : Nat → List String
  | 0 => [""]
  | n + 1 => "" :: (strings alphabet n).flatMap fun s => alphabet.map fun c => s.push c

/-- The characters XML treats specially, and one of each ordinary kind. -/
def special : List Char :=
  ['&', '<', '>', '"', '\'', ']', '-', '!', '#', ';', '\t', '\n', '\r', ' ', 'x', 'é', '𝔘']

-- Every text of up to three such characters; the empty text is not a tree `parse` produces.
#guard ((strings special 3).filter (· != "")).all fun s => roundTrips (text s)
-- Every attribute value of up to three such characters.
#guard (strings special 3).all fun s => roundTrips (attr s)
-- Every comment of up to three such characters that XML allows.
#guard (strings special 3).all fun s =>
  let e := elem "a" [] #[.Comment s]
  if (s.splitOn "--").length > 1 || s.endsWith "-" || s.contains (· == '\r') then err e == some (.invalidComment s)
  else roundTrips e

#guard roundTrips (text "&lt;not a tag&gt; &#38; <![CDATA[ not a section ]]>")
#guard roundTrips (text "  leading and trailing space  ")
#guard roundTrips (elem "a")
#guard roundTrips (elem "tbx" [("type", "TBX-Basic"), ("xml:lang", "en"), ("xmlns", "urn:iso:std:iso:30042:ed-2")]
  #[.Element (elem "termEntry" [("id", "c<1>&\"2\"")]
      #[.Character "\n  ", .Comment " R&D ", .Element (elem "term" [] #[.Character "AT&T <\"R&D\">"]),
        .Character " tail ", .Element (elem "note"), .Comment "", .Comment "x"]),
    .Element (elem "empty")])

-- A tree with empty or adjacent character data is read back joined.
#guard roundTripsToNormal (elem "a" [] #[.Character "x", .Character "", .Character "<y>",
  .Element (elem "b" [] #[.Character ""]), .Character "", .Comment "c", .Character "z"])
#guard (elem "a" [] #[.Character "x", .Character "", .Character "y", .Element (elem "b" [] #[.Character ""])]).normalize
  == elem "a" [] #[.Character "xy", .Element (elem "b")]
#guard (strings ['&', '<', 'x'] 2).all fun s => (strings ['>', '\r', 'y'] 2).all fun t =>
  roundTripsToNormal (elem "a" [] #[.Character s, .Character t, .Element (text s), .Character t])

/-! ## Reading: an element without content has none, however it is written -/

#guard (parse "<a></a>").toOption == some (elem "a")
#guard (parse "<a><b/><c></c></a>").toOption == some (elem "a" [] #[.Element (elem "b"), .Element (elem "c")])
#guard (parse "<a><![CDATA[]]></a>").toOption == some (elem "a")
#guard (parse "<a> <b/> </a>").toOption
  == some (elem "a" [] #[.Character " ", .Element (elem "b"), .Character " "])

end LeanXmlTest

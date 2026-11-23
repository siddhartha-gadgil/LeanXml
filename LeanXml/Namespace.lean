/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanXml.Basic
import LeanXml.Parser

/-!
# Resolution of namespace declarations

This module implements [Namespaces in XML 1.0 (Third Edition)](https://www.w3.org/TR/xml-names/)
over the tree of `LeanXml.Basic`.

The parser of `LeanXml.Parser` is not namespace-aware: an `Element` carries its name and the
names of its attributes as written in the document (`tbx:term`, `xml:lang`), and the namespace
declarations (`xmlns`, `xmlns:tbx`) are ordinary entries of its `Attributes`.

`Element.resolveNamespaces` turns such a tree into a `ResolvedElement`: a tree of the same
shape in which every element and attribute has an `ExpandedName` (namespace name and local
name), so that a reader identifies them whatever prefix the document chose. The existing
`Element` type and the output of the parser are unchanged; `ResolvedElement.toElement` gives
back the tree that was resolved.

The rules: a declaration is in scope in the element that makes it (its own name and attributes
included) and in its descendants unless overridden; an unprefixed element name is in the
default namespace, an unprefixed attribute name is in no namespace, and `xmlns=""` undeclares
the default namespace; `xml` is bound to `xmlNamespace` without a declaration and `xmlns` is
not a prefix a name can have; `xmlns` and `xmlns:*` attributes are `declarations`, not
`attributes`.
-/

namespace Lean
namespace Xml

/-- The namespace name the prefix `xml` is bound to, in every document
(<https://www.w3.org/TR/xml-names/#xmlReserved>). -/
def xmlNamespace : String := "http://www.w3.org/XML/1998/namespace"

/-- The namespace name the prefix `xmlns` is bound to; it cannot be declared, and no name can
be in it (<https://www.w3.org/TR/xml-names/#xmlReserved>). -/
def xmlnsNamespace : String := "http://www.w3.org/2000/xmlns/"

/-- An expanded name: a namespace name and a local name
(<https://www.w3.org/TR/xml-names/#dt-expname>). `ns` is `none` for a name that is in no
namespace. Two names are equal when both parts are; the prefix is not part of the name. -/
structure ExpandedName where
  ns : Option String := none
  localName : String
deriving DecidableEq, Hashable, Ord, Repr, Inhabited

/-- Clark notation: `{namespace-name}local`, or `local` for a name in no namespace. -/
instance : ToString ExpandedName where
  toString
    | ⟨some ns, l⟩ => "{" ++ ns ++ "}" ++ l
    | ⟨none, l⟩ => l

/-- What makes a well-formed document not namespace-well-formed. -/
inductive NamespaceError where
  /-- The name is not a `QName` (<https://www.w3.org/TR/xml-names/#NT-QName>): it has more than
  one colon, or an empty prefix or local part, or a local part that cannot start a name. -/
  | malformedQName (qname : String)
  /-- The prefix of `qname` has no declaration in scope
  (<https://www.w3.org/TR/xml-names/#nsc-NSDeclared>). -/
  | undeclaredPrefix (pfx : String) (qname : String)
  /-- `xmlns:xml` is declared with a namespace name other than `xmlNamespace`. -/
  | xmlPrefixRebound (uri : String)
  /-- `xmlns:xmlns` is declared. -/
  | xmlnsPrefixDeclared
  /-- `xmlNamespace` or `xmlnsNamespace` is bound to another prefix (`some pfx`) or declared as
  the default namespace (`none`). -/
  | reservedNamespaceBound (pfx : Option String) (uri : String)
  /-- `xmlns:pfx=""`: in Namespaces in XML 1.0 only the default namespace can be undeclared
  (<https://www.w3.org/TR/xml-names/#nsc-NoPrefixUndecl>). -/
  | prefixUndeclared (pfx : String)
  /-- An element name has the prefix `xmlns`. -/
  | xmlnsElementPrefix (qname : String)
  /-- Two attributes of one element have the same expanded name
  (<https://www.w3.org/TR/xml-names/#uniqAttrs>). -/
  | duplicateAttribute (name : ExpandedName) (qname₁ qname₂ : String)
deriving DecidableEq, Repr, Inhabited

instance : ToString NamespaceError where
  toString
    | .malformedQName q => s!"'{q}' is not a qualified name"
    | .undeclaredPrefix p q => s!"the prefix '{p}' of '{q}' is not declared"
    | .xmlPrefixRebound uri =>
      s!"the prefix 'xml' cannot be bound to '{uri}': it is bound to '{xmlNamespace}'"
    | .xmlnsPrefixDeclared => "the prefix 'xmlns' cannot be declared"
    | .reservedNamespaceBound (some p) uri =>
      s!"the reserved namespace name '{uri}' cannot be bound to the prefix '{p}'"
    | .reservedNamespaceBound none uri =>
      s!"the reserved namespace name '{uri}' cannot be the default namespace"
    | .prefixUndeclared p =>
      s!"the prefix '{p}' cannot be undeclared: 'xmlns:{p}' has an empty value"
    | .xmlnsElementPrefix q => s!"the element name '{q}' has the prefix 'xmlns'"
    | .duplicateAttribute n q₁ q₂ =>
      s!"the attributes '{q₁}' and '{q₂}' have the same expanded name {n}"

/-- Characters that can continue a name but not start one
(<https://www.w3.org/TR/xml/#NT-NameChar>). -/
private def isNameCharOnly (c : Char) : Bool :=
  c.isDigit || c == '-' || c == '.' || c == '\xB7'
    || ('\u0300' ≤ c && c ≤ '\u036F') || ('\u203F' ≤ c && c ≤ '\u2040')

/-- Split a name of the document into its prefix, if it has one, and its local part
(<https://www.w3.org/TR/xml-names/#NT-QName>). The argument is assumed to be a `Name` of
XML 1.0, as the parser guarantees. -/
def splitQName (qname : String) : Except NamespaceError (Option String × String) :=
  let startsName (s : String) : Bool :=
    match s.toList with
    | [] => false
    | c :: _ => !isNameCharOnly c
  match qname.splitOn ":" with
  | [l] => if startsName l then pure (none, l) else throw (.malformedQName qname)
  | [p, l] =>
    if startsName p && startsName l then pure (some p, l) else throw (.malformedQName qname)
  | _ => throw (.malformedQName qname)

/-- A namespace declaration attribute (<https://www.w3.org/TR/xml-names/#ns-decl>):
`xmlns:pfx="uri"` when `pfx` is `some pfx`, `xmlns="uri"` when it is `none`. `xmlns=""`, which
undeclares the default namespace, has the empty `uri`. -/
structure NamespaceDeclaration where
  pfx : Option String
  uri : String
deriving DecidableEq, Repr, Inhabited

/-- The name of the attribute that makes the declaration: `xmlns` or `xmlns:pfx`. -/
def NamespaceDeclaration.attributeName : NamespaceDeclaration → String
  | ⟨none, _⟩ => "xmlns"
  | ⟨some p, _⟩ => "xmlns:" ++ p

/-- The namespace declarations in scope at a point of a document
(<https://www.w3.org/TR/xml-names/#scoping>). -/
structure NamespaceScope where
  /-- The default namespace, `none` when there is none or it was undeclared by `xmlns=""`. -/
  defaultNamespace : Option String := none
  /-- The declared prefixes and their namespace names. `xml` is not listed: it is always
  bound. -/
  prefixes : Std.TreeMap String String := {}
deriving Repr, Inhabited

namespace NamespaceScope

/-- The scope outside the root element: no default namespace, and only `xml` bound. -/
def initial : NamespaceScope := {}

/-- The namespace name a prefix is bound to. `xml` is always bound to `xmlNamespace`. -/
def lookup (scope : NamespaceScope) (pfx : String) : Option String :=
  if pfx == "xml" then some xmlNamespace else scope.prefixes.get? pfx

/-- Add one declaration, which overrides the declaration of the same prefix (or of the
default namespace) of the enclosing scope. -/
def declare (scope : NamespaceScope) (d : NamespaceDeclaration) :
    Except NamespaceError NamespaceScope :=
  match d.pfx with
  | none =>
    if d.uri == xmlNamespace || d.uri == xmlnsNamespace then
      throw (.reservedNamespaceBound none d.uri)
    else
      pure { scope with defaultNamespace := if d.uri.isEmpty then none else some d.uri }
  | some p =>
    if p == "xmlns" then throw .xmlnsPrefixDeclared
    else if p == "xml" then
      if d.uri == xmlNamespace then pure scope else throw (.xmlPrefixRebound d.uri)
    else if d.uri.isEmpty then throw (.prefixUndeclared p)
    else if d.uri == xmlNamespace || d.uri == xmlnsNamespace then
      throw (.reservedNamespaceBound (some p) d.uri)
    else pure { scope with prefixes := scope.prefixes.insert p d.uri }

/-- The expanded name of an element whose name in the document is `qname`: an unprefixed
element name is in the default namespace (<https://www.w3.org/TR/xml-names/#defaulting>). -/
def resolveElementName (scope : NamespaceScope) (qname : String) :
    Except NamespaceError ExpandedName := do
  match ← splitQName qname with
  | (none, l) => pure ⟨scope.defaultNamespace, l⟩
  | (some p, l) =>
    if p == "xmlns" then throw (.xmlnsElementPrefix qname)
    match scope.lookup p with
    | some uri => pure ⟨some uri, l⟩
    | none => throw (.undeclaredPrefix p qname)

/-- The expanded name of an attribute whose name in the document is `qname`: the default
namespace does not apply, so an unprefixed attribute name is in no namespace
(<https://www.w3.org/TR/xml-names/#defaulting>). Not for `xmlns` and `xmlns:*`, which are
declarations and have no expanded name here. -/
def resolveAttributeName (scope : NamespaceScope) (qname : String) :
    Except NamespaceError ExpandedName := do
  match ← splitQName qname with
  | (none, l) => pure ⟨none, l⟩
  | (some p, l) =>
    match scope.lookup p with
    | some uri => pure ⟨some uri, l⟩
    | none => throw (.undeclaredPrefix p qname)

end NamespaceScope

/-- The declaration an attribute of the parsed tree makes, if its name is `xmlns` or
`xmlns:pfx`. -/
def namespaceDeclaration? (qname value : String) :
    Except NamespaceError (Option NamespaceDeclaration) := do
  match ← splitQName qname with
  | (none, "xmlns") => pure (some ⟨none, value⟩)
  | (some "xmlns", p) => pure (some ⟨some p, value⟩)
  | _ => pure none

/-- An attribute that is not a namespace declaration, with its expanded name. -/
structure ResolvedAttribute where
  name : ExpandedName
  /-- The name as written in the document. -/
  qname : String
  value : String
deriving DecidableEq, Repr, Inhabited

mutual
/-- An element whose names are resolved; see `Element.resolveNamespaces`. -/
inductive ResolvedElement
  | mk
    (name : ExpandedName)
    (qname : String)
    (attributes : Array ResolvedAttribute)
    (declarations : Array NamespaceDeclaration)
    (scope : NamespaceScope)
    (content : Array ResolvedContent)

/-- The content of a `ResolvedElement`: `Content` with resolved elements. -/
inductive ResolvedContent
  | element (element : ResolvedElement)
  | comment (comment : String)
  | character (content : String)
deriving Inhabited
end

namespace ResolvedElement

/-- The expanded name of the element. -/
def name : ResolvedElement → ExpandedName
  | mk n .. => n

/-- The name of the element as written in the document. -/
def qname : ResolvedElement → String
  | mk _ q .. => q

/-- The attributes other than namespace declarations, in the order of `Attributes`. -/
def attributes : ResolvedElement → Array ResolvedAttribute
  | mk _ _ as .. => as

/-- The namespace declarations made on the element itself. -/
def declarations : ResolvedElement → Array NamespaceDeclaration
  | mk _ _ _ ds .. => ds

/-- The declarations in scope in the element, its own included: what resolves a qualified
name found in an attribute value or in character content. -/
def scope : ResolvedElement → NamespaceScope
  | mk _ _ _ _ s _ => s

def content : ResolvedElement → Array ResolvedContent
  | mk _ _ _ _ _ c => c

/-- Whether the element has this namespace name and local name. -/
def is (e : ResolvedElement) (ns : Option String) (localName : String) : Bool :=
  e.name == ⟨ns, localName⟩

/-- The value of the attribute with this namespace name and local name. An unprefixed
attribute has `ns := none`; `xml:lang` has `ns := some xmlNamespace`. -/
def attribute? (e : ResolvedElement) (ns : Option String) (localName : String) :
    Option String :=
  e.attributes.find? (·.name == ⟨ns, localName⟩) |>.map (·.value)

/-- The child elements, in document order. -/
def childElements (e : ResolvedElement) : Array ResolvedElement :=
  e.content.filterMap fun
    | .element c => some c
    | _ => none

/-- The child elements with this namespace name and local name, in document order. -/
def childElementsNamed (e : ResolvedElement) (ns : Option String) (localName : String) :
    Array ResolvedElement :=
  e.childElements.filter (·.is ns localName)

end ResolvedElement

mutual
/-- The tree `e` was resolved from: `(← e.resolveNamespaces).toElement` is `e`. -/
def ResolvedElement.toElement : ResolvedElement → Element
  | .mk _ qname attributes declarations _ content =>
    let as : Std.TreeMap String String :=
      attributes.foldl (fun m a => m.insert a.qname a.value) {}
    let as := declarations.foldl (fun m d => m.insert d.attributeName d.uri) as
    .Element qname as (content.map ResolvedContent.toContent)

/-- The content `c` was resolved from. -/
def ResolvedContent.toContent : ResolvedContent → Content
  | .element e => .Element e.toElement
  | .comment c => .Comment c
  | .character c => .Character c
end

mutual
/-- Resolve the namespace declarations of `e` and its descendants; `scope` is the scope outside `e`.
Resolution stops at the first error, in document order. -/
def Element.resolveNamespaces (e : Element)
    (scope : NamespaceScope := NamespaceScope.initial) :
    Except NamespaceError ResolvedElement := do
  let .Element qname attrs content := e
  let mut declarations : Array NamespaceDeclaration := #[]
  let mut plain : Array (String × String) := #[]
  for (n, v) in attrs.toArray do
    match ← namespaceDeclaration? n v with
    | some d => declarations := declarations.push d
    | none => plain := plain.push (n, v)
  let scope ← declarations.foldlM NamespaceScope.declare scope
  let name ← scope.resolveElementName qname
  let mut attributes : Array ResolvedAttribute := #[]
  for (n, v) in plain do
    let an ← scope.resolveAttributeName n
    if let some other := attributes.find? (·.name == an) then
      throw (.duplicateAttribute an other.qname n)
    attributes := attributes.push ⟨an, n, v⟩
  let content ← content.mapM (·.resolveNamespaces scope)
  pure (.mk name qname attributes declarations scope content)

/-- Resolve the namespace declarations of the elements of `c`, in the scope `scope`. -/
def Content.resolveNamespaces (c : Content) (scope : NamespaceScope) :
    Except NamespaceError ResolvedContent :=
  match c with
  | .Element e => .element <$> e.resolveNamespaces scope
  | .Comment s => pure (.comment s)
  | .Character s => pure (.character s)
end

/-- Parse a document and resolve its namespace declarations: `parse`, then
`Element.resolveNamespaces`. The error is the parser's, or a `NamespaceError` as text. -/
def parseResolved (s : String) : Except String ResolvedElement := do
  let e ← parse s
  match e.resolveNamespaces with
  | .ok r => pure r
  | .error err => throw (toString err)

end Xml
end Lean

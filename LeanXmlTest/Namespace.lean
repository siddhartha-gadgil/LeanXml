/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanXml.Namespace

/-!
# Tests of namespace resolution

Each `#guard` is one case of [Namespaces in XML 1.0](https://www.w3.org/TR/xml-names/); the
build of this module fails if one does not hold.
-/

namespace LeanXmlTest.Namespace
open Lean.Xml

/-- A resolved tree as text: `(name @attribute=value … child …)`, names in Clark notation.
Character content and comments are left out. -/
partial def render (e : ResolvedElement) : String :=
  let attrs := e.attributes.foldl (fun s a => s ++ s!" @{a.name}={a.value}") ""
  let children := e.childElements.foldl (fun s c => s ++ " " ++ render c) ""
  s!"({e.name}{attrs}{children})"

/-- The rendering of the document `src`, or the error as text. -/
def tree (src : String) : String :=
  match parseResolved src with
  | .ok e => render e
  | .error m => "error: " ++ m

/-- The namespace error of the document `src`, if it parses and has one. -/
def nsError (src : String) : Option NamespaceError :=
  match parse src with
  | .ok e =>
    match e.resolveNamespaces with
    | .ok _ => none
    | .error err => some err
  | .error _ => none

/-- Whether `src` parses: guards the cases below against passing for a parse error. -/
def parses (src : String) : Bool :=
  match parse src with
  | .ok _ => true
  | .error _ => false

/-! ## Names without namespaces -/

#guard tree "<a b='1'><c/>text<!-- c --><d e='2'/></a>" = "(a @b=1 (c) (d @e=2))"

/-! ## Default namespace (§6.2)

It applies to the element that declares it and to its descendants, and not to attributes. -/

#guard tree "<a xmlns='urn:u' b='1'><c d='2'/></a>" = "({urn:u}a @b=1 ({urn:u}c @d=2))"

/-! `xmlns=""` undeclares it, for the element that says so and its descendants only. -/

#guard tree "<a xmlns='urn:u'><b xmlns=''><c/></b><d/></a>" = "({urn:u}a (b (c)) ({urn:u}d))"

/-! An inner default declaration overrides the outer one. -/

#guard tree "<a xmlns='urn:u'><b xmlns='urn:v'><c/></b><d/></a>"
  = "({urn:u}a ({urn:v}b ({urn:v}c)) ({urn:u}d))"

/-! ## Prefixes (§6.1)

The prefix is not part of the name: these two documents have the same names. -/

#guard tree "<t:a xmlns:t='urn:u'><t:b/></t:a>" = "({urn:u}a ({urn:u}b))"
#guard tree "<t:a xmlns:t='urn:u'><t:b/></t:a>" = tree "<a xmlns='urn:u'><b/></a>"
#guard tree "<x:a xmlns:x='urn:u'><y:b xmlns:y='urn:u'/></x:a>" = "({urn:u}a ({urn:u}b))"

/-! A declaration applies to the name and the attributes of the element that makes it. -/

#guard tree "<p:a p:b='1' c='2' xmlns:p='urn:u'/>" = "({urn:u}a @c=2 @{urn:u}b=1)"

/-! A prefixed attribute is in the namespace of its prefix, whatever the default namespace. -/

#guard tree "<a xmlns='urn:u' xmlns:p='urn:v' p:b='1' b='2'/>" = "({urn:u}a @b=2 @{urn:v}b=1)"

/-! An inner declaration overrides the outer one of the same prefix, in its subtree only. -/

#guard tree "<p:a xmlns:p='urn:u'><p:b xmlns:p='urn:v'><p:c/></p:b><p:d/></p:a>"
  = "({urn:u}a ({urn:v}b ({urn:v}c)) ({urn:u}d))"

/-! A declaration on an element is not in scope in its siblings or its parent. -/

#guard nsError "<a><b xmlns:p='urn:u'/><p:c/></a>" = some (.undeclaredPrefix "p" "p:c")
#guard nsError "<p:a><b xmlns:p='urn:u'/></p:a>" = some (.undeclaredPrefix "p" "p:a")

/-! ## Undeclared prefix (§5, Namespace constraint: Prefix Declared) -/

#guard nsError "<p:a/>" = some (.undeclaredPrefix "p" "p:a")
#guard nsError "<a p:b='1'/>" = some (.undeclaredPrefix "p" "p:b")
#guard nsError "<a xmlns='urn:u'><b><q:c/></b></a>" = some (.undeclaredPrefix "q" "q:c")
#guard tree "<p:a/>" = "error: the prefix 'p' of 'p:a' is not declared"

/-! ## The prefix `xml` (§3)

It is bound without a declaration, in elements and attributes. -/

#guard tree "<a xml:lang='en'><xml:b/></a>"
  = "(a @{http://www.w3.org/XML/1998/namespace}lang=en ({http://www.w3.org/XML/1998/namespace}b))"

/-! It may be declared, with its own namespace name only. -/

#guard tree "<a xmlns:xml='http://www.w3.org/XML/1998/namespace' xml:lang='en'/>"
  = "(a @{http://www.w3.org/XML/1998/namespace}lang=en)"
#guard nsError "<a xmlns:xml='urn:u'/>" = some (.xmlPrefixRebound "urn:u")

/-! No other prefix, and no default declaration, may have its namespace name. -/

#guard nsError "<a xmlns:p='http://www.w3.org/XML/1998/namespace'/>"
  = some (.reservedNamespaceBound (some "p") xmlNamespace)
#guard nsError "<a xmlns='http://www.w3.org/XML/1998/namespace'/>"
  = some (.reservedNamespaceBound none xmlNamespace)

/-! ## The prefix `xmlns` (§3)

It cannot be declared, its namespace name cannot be bound, and no element can have it. -/

#guard nsError "<a xmlns:xmlns='http://www.w3.org/2000/xmlns/'/>" = some .xmlnsPrefixDeclared
#guard nsError "<a xmlns:xmlns='urn:u'/>" = some .xmlnsPrefixDeclared
#guard nsError "<a xmlns:p='http://www.w3.org/2000/xmlns/'/>"
  = some (.reservedNamespaceBound (some "p") xmlnsNamespace)
#guard nsError "<a xmlns='http://www.w3.org/2000/xmlns/'/>"
  = some (.reservedNamespaceBound none xmlnsNamespace)
#guard nsError "<xmlns:a/>" = some (.xmlnsElementPrefix "xmlns:a")

/-! ## A prefix cannot be undeclared (§5, Namespace constraint: No Prefix Undeclaring) -/

#guard nsError "<a xmlns:p='urn:u'><b xmlns:p=''/></a>" = some (.prefixUndeclared "p")

/-! ## Qualified names (§4)

At most one colon, and a prefix and a local part that are names. -/

#guard parses "<a:b:c xmlns:a='urn:u'/>" && nsError "<a:b:c xmlns:a='urn:u'/>"
  = some (.malformedQName "a:b:c")
#guard parses "<:a/>" && nsError "<:a/>" = some (.malformedQName ":a")
#guard parses "<a:/>" && nsError "<a:/>" = some (.malformedQName "a:")
#guard parses "<a:1b xmlns:a='urn:u'/>" && nsError "<a:1b xmlns:a='urn:u'/>"
  = some (.malformedQName "a:1b")
#guard nsError "<a b:c:d='1'/>" = some (.malformedQName "b:c:d")
#guard nsError "<a xmlns:='urn:u'/>" = some (.malformedQName "xmlns:")
#guard (splitQName "a").toOption = some (none, "a")
#guard (splitQName "p:a").toOption = some (some "p", "a")

/-! ## Uniqueness of attributes (§6.3)

The two cases of the recommendation: the first pair of documents is in error, the second is
not, because the default namespace does not apply to attributes. -/

#guard nsError "<x xmlns:n1='urn:u' xmlns:n2='urn:u'><bad n1:a='1' n2:a='2'/></x>"
  = some (.duplicateAttribute ⟨some "urn:u", "a"⟩ "n1:a" "n2:a")
#guard tree "<x xmlns:n1='urn:u' xmlns='urn:u'><good a='1' n1:a='2'/></x>"
  = "({urn:u}x ({urn:u}good @a=1 @{urn:u}a=2))"

/-! ## Declarations are not attributes; the scope is kept -/

/-- `f` applied to the resolved root of `src`. -/
def onRoot (src : String) (f : ResolvedElement → α) : Option α :=
  match parseResolved src with
  | .ok e => some (f e)
  | .error _ => none

def twoDecls : String := "<a xmlns='urn:u' xmlns:p='urn:v' b='1'><c xmlns:q='urn:w'/></a>"

#guard onRoot twoDecls (·.attributes.map (·.qname)) = some #["b"]
#guard onRoot twoDecls (·.declarations) = some #[⟨none, "urn:u"⟩, ⟨some "p", "urn:v"⟩]
#guard onRoot twoDecls (·.scope.lookup "p") = some (some "urn:v")
#guard onRoot twoDecls (·.scope.lookup "q") = some none
#guard onRoot twoDecls (·.scope.lookup "xml") = some (some xmlNamespace)
#guard onRoot twoDecls (·.scope.defaultNamespace) = some (some "urn:u")
#guard onRoot twoDecls (·.childElements.map (·.scope.lookup "q")) = some #[some "urn:w"]
#guard onRoot twoDecls (·.childElements.map (·.scope.lookup "p")) = some #[some "urn:v"]

/-! A qualified name in content is resolved with the scope of its element. -/

#guard onRoot twoDecls (·.scope.resolveElementName "p:x" |>.toOption)
  = some (some ⟨some "urn:v", "x"⟩)

/-! ## Relation to the parsed tree

`toElement` gives back the tree that was resolved, declarations included. -/

def roundTrips (src : String) : Bool :=
  match parse src with
  | .ok e =>
    match e.resolveNamespaces with
    | .ok r => toString r.toElement == toString e
    | .error _ => false
  | .error _ => false

#guard roundTrips twoDecls
#guard roundTrips "<p:a xmlns:p='urn:u' xml:lang='en' p:b='1'>t<!-- c --><b xmlns=''>u</b></p:a>"
#guard onRoot twoDecls (·.qname) = some "a"

/-! A subtree is resolved in the scope of its context. -/

def inScope (src : String) (scope : NamespaceScope) : Option String :=
  match parse src with
  | .ok e =>
    match e.resolveNamespaces scope with
    | .ok r => some (render r)
    | .error err => some ("error: " ++ toString err)
  | .error _ => none

#guard inScope "<p:a><b/></p:a>" { defaultNamespace := some "urn:u", prefixes := {("p", "urn:v")} }
  = some "({urn:v}a ({urn:u}b))"
#guard inScope "<p:a/>" .initial = some "error: the prefix 'p' of 'p:a' is not declared"

/-! ## An ISO 30042 (TBX) document

The same names whether the TBX namespace is the default namespace or has a prefix; `xml:lang`
is found by its namespace name; an element of another namespace is told apart. -/

def tbx : String := "urn:iso:std:iso:30042:ed-2"

def tbxDefault : String := "<?xml version='1.0' encoding='UTF-8'?>
<tbx type='TBX-Basic' style='dca' xml:lang='en' xmlns='urn:iso:std:iso:30042:ed-2'>
  <text><body>
    <conceptEntry id='c1'>
      <langSec xml:lang='fr'><termSec><term>terme</term></termSec></langSec>
      <m:math xmlns:m='http://www.w3.org/1998/Math/MathML'><m:mi>x</m:mi></m:math>
    </conceptEntry>
  </body></text>
</tbx>"

def tbxPrefixed : String := "<t:tbx type='TBX-Basic' style='dca' xml:lang='en'
    xmlns:t='urn:iso:std:iso:30042:ed-2' xmlns='http://www.w3.org/1998/Math/MathML'>
  <t:text><t:body>
    <t:conceptEntry id='c1'>
      <t:langSec xml:lang='fr'><t:termSec><t:term>terme</t:term></t:termSec></t:langSec>
      <math><mi>x</mi></math>
    </t:conceptEntry>
  </t:body></t:text>
</t:tbx>"

#guard tree tbxDefault = "({urn:iso:std:iso:30042:ed-2}tbx @style=dca @type=TBX-Basic \
@{http://www.w3.org/XML/1998/namespace}lang=en ({urn:iso:std:iso:30042:ed-2}text \
({urn:iso:std:iso:30042:ed-2}body ({urn:iso:std:iso:30042:ed-2}conceptEntry @id=c1 \
({urn:iso:std:iso:30042:ed-2}langSec @{http://www.w3.org/XML/1998/namespace}lang=fr \
({urn:iso:std:iso:30042:ed-2}termSec ({urn:iso:std:iso:30042:ed-2}term))) \
({http://www.w3.org/1998/Math/MathML}math ({http://www.w3.org/1998/Math/MathML}mi))))))"
#guard tree tbxPrefixed = tree tbxDefault

#guard onRoot tbxDefault (·.is (some tbx) "tbx") = some true
#guard onRoot tbxPrefixed (·.is (some tbx) "tbx") = some true
#guard onRoot tbxPrefixed (·.is none "tbx") = some false
#guard onRoot tbxPrefixed (·.attribute? (some xmlNamespace) "lang") = some (some "en")
#guard onRoot tbxPrefixed (·.attribute? none "type") = some (some "TBX-Basic")
#guard onRoot tbxPrefixed (·.attribute? none "lang") = some none
#guard onRoot tbxPrefixed (·.childElementsNamed (some tbx) "text" |>.size) = some 1
#guard onRoot tbxPrefixed (·.childElementsNamed none "text" |>.size) = some 0

end LeanXmlTest.Namespace

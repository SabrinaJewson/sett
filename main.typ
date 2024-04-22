#set heading(numbering: "1.")

= The Type Theory of Sett

#let id(..t) = text(font: "DejaVu Sans", size: 9pt, ..t)
#let TT = math.upright("T")
#let Eq = id("Eq")
#let Prop = id("Prop")
#let funext = id("funext")
#let elim = id("elim")
#let elimpair = $id("elim_pair")$
#let elimnode = id("elim_node")
#let elimbranch = id("elim_branch")
#let node = id("node")
#let branch = id("branch")
#let lelim = id("large_elim")
#let lelimnode = id("large_elim_node")
#let lelimbranch = id("large_elim_branch")
#let refl = id("refl")
#let elimrefl = id("elim_refl")
#let KK = id("K")
#let El = id("El")
#let propresize = id("propresize")
#let ctx = id("ctx")
#let Type = id("Type")
#let sort = id("sort")
#let Sigma = id("Sigma")
#let pair = id("pair")
#let Tree = id("Tree")
#let hide = hide
#let IsProp = id("IsProp")
#let Injective = id("Injective")
#let Surjective = id("Surjective")
#let Bijective = id("Bijective")
#let Bool = id("Bool")
#let Sum = id("Sum")
#let em = id("em")
#let choice = id("choice")

We denote variables $x$, constants $c$,
expressions $e$, $f$, $α$, $β$, and contexts $Γ$.

$
e, f, α, β &::= x | c | Π x : α. med e | λ x : α. med e | f med e | Type
\ Γ &::= · | Γ, x : e
$

There are four kinds of judgement:

$ Γ ctx #h(5em) Γ ⊢ α sort #h(5em) Γ ⊢ e : α #h(5em) Γ ⊢ e ≡ e' $

The empty context is well-formed, and contexts may be extended with variables:

$ ()/(· ctx) #h(7em) (Γ ⊢ α sort)/((Γ, x : α) ctx) med ("where" x ∉ Γ) $

Every type is a sort, as is $Type$ itself:

$ (Γ ⊢ α : Type)/(Γ ⊢ α sort) #h(7em) (Γ ctx)/(Γ ⊢ Type sort) $

Typing judgements are invariant under context extensions,
and may be derived from $Γ$ and $≡$.

$
  ((Γ, x : α) ctx quad Γ ⊢ e : β) / (Γ, x : α ⊢ e : β) #h(4em)
  (Γ ⊢ α sort) / (Γ, x : α ⊢ x : α) #h(4em)
  (Γ ⊢ e : α quad Γ ⊢ α ≡ β) / (Γ ⊢ e : β)
$

Judgemental equality is defined inductively for (valid) expressions.

$
  (Γ ⊢ x : α) / (Γ ⊢ x ≡ x) #h(3em)
  (Γ ctx) / (Γ ⊢ c ≡ c) #h(3em)
  (Γ ctx) / (Γ ⊢ Type ≡ Type) #h(3em)

 (Γ ⊢ f ≡ f' quad Γ ⊢ e ≡ e' quad Γ ⊢ f med e : α) /
  (Γ ⊢ f med e ≡ f' med e') $
$
  (Γ ⊢ α ≡ α' quad Γ, x : α ⊢ e ≡ e' quad Γ ⊢ Π x : α. med e sort)
  / (Γ ⊢ Π x : α. med e ≡ Π x : α'. med e') #h(1em)
  (Γ ⊢ α ≡ α' quad Γ, x : α ⊢ e ≡ e' quad Γ ⊢ λ x : α. med e : β)
  / (Γ ⊢ λ x : α. med e ≡ λ x : α'. med e')
$

$
  (Γ ⊢ (λ x : α. med e) med e' : β) / (Γ ⊢ (λ x : α. med e) med e' ≡ e[e' \/ x]) #h(4em)
  (Γ ⊢ (λ x : α. med e) med e' : β) / (Γ ⊢ e[e' \/ x] ≡ (λ x : α. med e) med e')
$

Hence, judgemental equality is reflexive, symmetric and transitive.
The last two rules define our only reduction rule in this type theory, β-reduction.

Next we define the typing rules of functions:
small $Π$-types live in $Type$, but large ones are only sorts;
they are introduced by $λ$, and eliminated by application.

$ (Γ ⊢ α : Type quad Γ, x : α ⊢ e : Type) / (Γ ⊢ Π x : α. med e : Type) #h(4em)
  (Γ, x : α ⊢ e sort) / (Γ ⊢ Π x : α. med e sort) $
$ (Γ, x : α ⊢ e : β) / (Γ ⊢ λ x : α. med e : Π x : α. med β) #h(4em)
  (Γ ⊢ f : Π x : α. med β quad Γ ⊢ e : α) / (Γ ⊢ f med e : β[e \/ x])
$

Now we introduce the 22 constants of the language.

$
c ::= &Eq | refl | elim_= | elimrefl | KK | funext
\ | &Sigma | pair | elim_Σ | elimpair
\ | &ℙ | El_ℙ | propresize
\ | &Tree | node | branch | elim_TT | elimnode | elimbranch
\ | &lelim_TT | lelimnode | lelimbranch
$

We add some notation for convenience:

- $Π (x_0 : α_0) … (x_n : α_n). med β := Π x_0 : α_0. … Π x_n : α_n. med β$;
- $Π (x_0 … x_n : α). med β := Π (x_0 : α) … (x_n : α). med β$;
- $Σ x : α. med β := Sigma med α med (λ x: α. med β)$ and $TT x : α. med β := Tree med α med (λ x: α. med β)$;
- $α → β := Π x : α. med β$, and likewise $α × β := Σ x : α. med β$,
  where $x$ is not free in $β$;
- $e = e' := Eq med α med e med e'$, where $e : α$;
- we omit function parameters in applications when they can be inferred;
- the types of binders may similarly be omitted when inferrable.

Each constant has a typing rule.
For brevity, they are expressed below as a list;
each entry can be taken as a judgement true for the empty context.
We begin with the axioms of equality, with the type former $Eq$,
its reflexivity, the principle of based path induction,
and its reduction rule;
we postulate axiom K (the unicity of identity proofs)
and well as function extensionality.

- $Eq : Π α : Type. med α → α → Type$
- $refl : Π (α : Type) (a : α). med a = a$
- $elim_= : Π (α : Type) (a : α) (C : Π b. med a = b → Type)
  (h : C med a med (refl med a)) (b : α) (t : a = b). med C med b med t $
- $elimrefl : Π (α : Type) (a : α) (C : Π b. med a = b → Type)
  (h : C med a med (refl med a)). med elim_= med h med (refl med a) = h$
- $KK : Π (α : Type) (a med b : α) (h med h' : a = b). med h = h'$
- $funext : Π (α : Type) (β : α → Type) (f med g : Π a. med β med a)
  (h : Π x. med f med x = g med x). med f = g$

Next is the $Σ$-type,
defined for simplicity in terms of an eliminator rather than projections.

- $Sigma : Π (α : Type) (β : α → Type). med Type$
- $pair : Π (α : Type) (β : α → Type) (a : α) (b : β med a). med Sigma med α med β$
- $elim_Σ : Π (α : Type) (β : α → Type) (C : Sigma med α med β → Type)
  (f : Π a med b. med C med (pair med a med b)) $$
  hide(elim_Σ : Π) (t : Sigma med α med β). med C med t$
- $elimpair : Π (α : Type) (β : α → Type) (C : Sigma med α med β → Type)
  (f : Π a med b. med C med (pair med a med b)) $
  $ hide(elimpair : Π) (a : α) (b : β med a). med
  elim_Σ med f med (pair med a med b) = f med a med b$

We postulate a small Tarski universe $ℙ$,
intended as a universe of propositions.

- $ℙ : Type$
- $El_ℙ : ℙ → Type$

For the next few typing rules, we first must make some standard definitions.

- $IsProp med α := Π (a med b : α). med a = b$;
  a proposition is a type with no more than one element.
- $Prop := Σ P : ℙ. med IsProp med (El_ℙ med P) ×
  (Π (Q : ℙ). med IsProp med (El_ℙ med Q) →$$
hide(Prop := Σ P : ℙ. med IsProp med (El_ℙ med P) × "(")
  (El_ℙ med P → El_ℙ med Q) → (El_ℙ med Q → El_ℙ med P) → Q = P)$\
  As given by the axioms, the basic $ℙ$ type is “too large”:
  there is no guarantee that any element of it is _actually_ a proposition.
  Hence, we restrict the set to its elements we care about:
  the type of propositions is those elements of $ℙ$
  that are extensional propositions.
- $[α] := Π P : Prop. med (α → El_ℙ med P) → El_ℙ med P$ \
  The bracket type $[α]$, also known as the _propositional truncation_ of $α$,
  is inhabited precisely when $α$ is, and has at most one element.
  Propositional resizing enables us to use a Church encoding.
- $∃ x : α. med β med a := [Σ x : α. med β med a]$
- $∃! x : α. med β med a := (Σ x : α. med β med a) × IsProp med (Σ x : α. med β med a)$
- $Injective med f := Π x med y. med f med x = f med y → x = y$
- $Surjective med f := Π b. med ∃ a. med f med a = b$
- $Bijective med f := Injective med f × Surjective med f$
- $α ↔ β := Σ f : α → β. med Bijective med f$

We are now ready to state the propositional resizing axiom,
which gives $ℙ$ its power:

- $propresize : Π (α : Type). med IsProp med α → ∃! P : ℙ. med El_ℙ med P ↔ α$

In words, this states that for all propositions $α$,
there is a unique member of $ℙ$ of the same cardinality.
This tells us that the number of propositions is _small_,
enabling impredicative constructs like the powerset.

We postulate the $Tree$ type, which enables well-founded recursion.
It is simiar in spirit to the well-known $id("W")$-type,
but is additionally allowed to be a $node$,
which terminates the tree and stores no data.
This bundles booleans and $id("W")$-types into one,
so we only need one large eliminator.

- $Tree : Π (α : Type) (β : α → Type). med Type$
- $node : Π (α : Type) (β : α → Type). med Tree med α med β$
- $branch : Π (α : Type) (β : α → Type) (a : α) (b : β med a → Tree med α med β). med
  Tree med α med β$
- $elim_TT : Π (α : Type) (β : α → Type) (C : Tree med α med β → Type)
  $$hide(elim_TT : Π) (h_1 : C med node)
  (h_2 : Π a med b. med (Π i. med C med (b med i)) → C med (branch med a med b))
  (t : Tree med α med β). med C med t$
- $elimnode : Π (α : Type) (β : α → Type) (C : Tree med α med β → Type)
  $$hide(elimnode : Π) (h_1 : C med node)
  (h_2 : Π a med b. med (Π i. med C med (b med i)) → C med (branch med a med b)).
  $$hide(elimnode : Π) elim_TT med h₁ med h₂ med node = h₁$
- $elimbranch : Π (α : Type) (β : α → Type) (C : Tree med α med β → Type)
  $$hide(elimbranch : Π) (h_1 : C med node)
  (h_2 : Π a med b. med (Π i. med C med (b med i)) → C med (branch med a med b))
  $$hide(elimbranch : Π)(a : α) (b : β med a → Tree med α med β).
  $$hide(elimbranch : Π) elim_TT med h₁ med h₂ med (branch med a med b) =
  h₂ med a med b med (λ i . med elim_TT med h_1 med h_2 med (b med i))$

Finally, we add support for large elimination to $Tree$,
enabling the construction of certain large sets.

- $lelim_TT : Π (α : Type)(β : α → Type)
  $$hide(lelim_TT : Π)
    (h₁ : Type)
    (h₂ : Π a. med (β med a → Tree med α med β) → (β med a → Type) → Type)
  $$hide(lelim_TT : Π) (t : Tree med α med β). med Type$
- $lelimnode : Π (α : Type)(β : α → Type)
  $$hide(lelimnode : Π)
    (h₁ : Type)
    (h₂ : Π a. med (β med a → Tree med α med β) → (β med a → Type) → Type).
  $$hide(lelimnode : Π) lelim_TT med h₁ med h₂ med node ↔ h₁$
- $lelimbranch : Π (α : Type)(β : α → Type)
  $$hide(lelimbranch : Π)
    (h₁ : Type)
    (h₂ : Π a. med (β med a → Tree med α med β) → (β med a → Type) → Type)
  $$hide(lelimbranch : Π)
  (a : α) (b : β med a → Tree med α med β)
    .
  $$hide(lelimbranch : Π) lelim_TT med h₁ med h₂ med (branch med a med b) ↔
  h_2 med a med b med (λ i . med lelim_TT med h₁ med h₂ med (b med i))$

= Extra Axioms

The following axioms are not part of the base theory,
but can be postulated to prove certain theorems.
We first make some definitions:

- $π_1 := elim_Σ med (λ a med b. med a)$, the first projection for $Σ$-types.
- $El := λ P : Prop. med El_ℙ med (π_1 med P)$
- $bold(0) := Π P : Prop. med El P$, the type with no elements
  (Church-encoded with the statement “every proposition is true”).
- $bold(1) := bold(0) → bold(0)$
- $bold(2) := TT i : bold(1). med bold(0)$, the type of booleans.
- $Sum med α med β := Σ b : bold(2). med lelim_bold(2) med α med β med b$
  (the definition of $lelim_bold(2)$ is not given, but is trivial).
- $α ∨ β := [Sum med α med β]$
- $¬P := P → bold(0)$

The Law of Excluded Middle states that every proposition is either true or false.

- $em : ∀ P : ℙ. med P ∨ ¬P$

The Axiom of Choice postulates the existence of a choice function for any indexed type family.

- $choice : Π (α : Type) (β : α → Type) (h : Π a. med [β med a]). med [Π a. med β med a]$

= Translating Sett to ZFC

#let red(c) = text(color.red, c)
#let notred(c) = text(color.black, c)
#let bl(c) = text(color.blue, c)
#let sm(c) = text(size: 0.8em, c)
#let sg = sm($γ$)
#let TL = $class("large", upright(T))$

#show sym.emptyset: set text(font: "Fira Sans")

Given $Γ ⊢ e : α$, we define a translation $⟦Γ ⊢ e⟧sg$,
where $γ$ is a list of translated expressions for every variable in $Γ$.
The translation results in an ZFC expression exactly,
or any higher-order function on ZFC expressions.

We denote symbols in the language of ZFC in #red[red].
Take $red(•)$ to be any set whose identity is unimportant;
for example, $red(∅)$.
We denote functions in ZFC as $red((x ∈ X) ↦ f(x))$,
as it is necessary to specify the domain to be a function
(that the codomain is a set follows from replacement).
We denote the definite description operator $red(ι(x(notred(φ(red(x))))))$,
evaluating to the unique $red(x)$ such that $φ(red(x))$ if it exists,
and is undefined otherwise.

- $⟦Γ ⊢ x⟧sg$ is the element of $γ$ corresponding to $x$.
- $⟦Γ ⊢ Π x : α. med β⟧sg =
  red(product_(x ∈ notred(⟦Γ ⊢ α⟧sg)))
    ⟦Γ, x : α ⊢ β⟧ sm((γ, red(x))) $
- $⟦Γ ⊢ λ x : α. med e⟧sg = red((x ∈ notred(⟦Γ ⊢ α⟧sg)) ↦)
  ⟦Γ, x : α ⊢ e⟧ sm((γ, red(x)))$,
  \ if $Γ, x : α ⊢ e : β$ and $Γ ⊢ Π x : α. med β : Type$;
- $⟦Γ ⊢ λ x : α. med e⟧sg = x ↦ ⟦Γ, x : α ⊢ e⟧ sm((γ, x))$
  otherwise.
- $⟦Γ ⊢ f med e⟧sg = ⟦Γ ⊢ f⟧sg red((notred(⟦Γ ⊢ e⟧sg)))$,
  if $Γ ⊢ f : Π x : α. med β$ and $Γ ⊢ Π x : α. med β : Type$;
- $⟦Γ ⊢ f med e⟧sg = ⟦Γ ⊢ f⟧sg(⟦Γ ⊢ e⟧sg)$ otherwise.
- $⟦Γ ⊢ Eq⟧sg = α ↦ "Eq"$,
  where $"Eq"(a, b) = red({x ∈ {•} | notred(a) = notred(b)})$
- $⟦Γ ⊢ refl⟧sg = α ↦ red((a ∈ notred(α)) ↦ •)$
- $⟦Γ ⊢ elim_=⟧sg = α ↦ a ↦ C ↦ red(
    (h ∈ notred(C(a)(red(•)))) ↦
    (b ∈ notred(α)) ↦
    (t ∈ notred("Eq"(a, b))) ↦
    h)$
- $⟦Γ ⊢ elimrefl⟧sg = α ↦ a ↦ C ↦ red(
    (h ∈ notred(C(α)(red(•)))) ↦ •)$
- $⟦Γ ⊢ KK⟧sg = α ↦ red((a med b ∈ notred(α)) ↦
  (h med h' ∈ notred("Eq"(a, b))) ↦ •
  )$
- $⟦Γ ⊢ funext⟧sg = α ↦ β ↦ red(
    (f med g ∈ product_(a ∈ notred(α)) notred(β(red(a)))) ↦
    (h ∈ product_(x ∈ notred(α)) notred("Eq"(red(f(x)), red(g(x)))) ) ↦
    •
  )$
- $⟦Γ ⊢ Sigma⟧sg = α ↦ β ↦ red(sum_(a ∈ notred(α)) notred(β(red(a))))$
- $⟦Γ ⊢ pair⟧sg = α ↦ β ↦ red(
    (a ∈ notred(α)) ↦
    (b ∈ notred(β(red(a)))) ↦
    (a, b)
  )$
- $⟦Γ ⊢ elim_Σ⟧sg = α ↦ β ↦ C ↦ red(
    (f ∈ product_(a ∈ notred(α)) product_(b ∈ notred(β(red(a))))
      notred(C(red((a, b))))) ↦
    ((a, b) ∈ sum_(a ∈ notred(α)) notred(β(red(a)))) ↦
    f(a)(b)
  )$
- $⟦Γ ⊢ elimpair⟧sg = α ↦ β ↦ C ↦ red(
    (f ∈ product_(a ∈ notred(α)) product_(b ∈ notred(β(red(a))))
      notred(C(red((a, b))))) ↦
    (a ∈ notred(α)) ↦
    (b ∈ notred(β(red(a)))) ↦
    •
  )$
- $⟦Γ ⊢ ℙ⟧sg = red(cal(P)({•}))$; this is equal to $red({∅, {•}})$.
- $⟦Γ ⊢ El_ℙ⟧sg = P ↦ P$
- $⟦Γ ⊢ propresize⟧sg = α ↦ red(
    (h : product_(a med b ∈ notred(α))
      notred("Eq"(red(a), red(b)))) ↦
    ((notred([α]), (notred("untrunc"(α)), notred("bij"(α)))),
    notred("isprop"(α)))
  )$
  where:
  - $[α] = red({x ∈ {•} | notred(α) "is inhabited"})$
  - $"untrunc"(α) = red((x ∈ notred([α])) ↦ ι(x(x ∈ notred(α))))$
  - $"inj"(α) = red((x med y ∈ notred([α])) ↦
      (h ∈ notred("Eq"("untrunc"(α)red((x)), "untrunc"(α)red((y))))) ↦
      •)$
  - $"surj"(α) = red((b ∈ notred(α)) ↦ •)$
  - $"bij"(α) = red((notred("inj"(α)), notred("surj"(α))))$
  - $"isprop"(α) = red((a med b ∈ sum_(P ∈ cal(P)({•}))
      sum_(f : P → notred(α))
        notred("Injective"(red(f : P →) α)) ×
        notred("Surjective"(red(f : P →) α))) ↦ •)$
  - $"Injective"(f red(:) α red(→) β) = red(product_(x y ∈ notred(α))
      notred("Eq"(red(f(x)), red(f(y))))
      → notred("Eq"(red(x), red(y)))) $
  - $"Surjective"(f red(:) α red(→) β) = red(product_(b ∈ notred(β)))
      [red(sum_(a ∈ notred(α)) notred("Eq"(red(f(a)), b)))]$
- $⟦Γ ⊢ Tree⟧sg = α ↦ β ↦ TL_(a ∈ α) β(a)$ \
  where:
  - $TL_(a ∈ α) β(a) = red({x ∈ V_notred(λ) |
    ∀ T, • ∈ T ∧ (∀ a med b,
      a ∈ notred(α) ∧ b : notred(β(red(a))) → T ⇒ (a, b) ∈ T) ⇒
      x ∈ T})$
  - $λ$ is some ordinal whose cofinality is greater than
    $red(sup_(a ∈ notred(α))(notred(β(red(a)))))$.
- $⟦Γ ⊢ node⟧sg = α ↦ β ↦ red(•)$
- $⟦Γ ⊢ branch⟧sg = α ↦ β ↦ red(
    (a ∈ notred(α)) ↦
    (b : notred(β(red(a))) → notred(TL_(a ∈ α) β(a))) ↦
    (a, b)
  )$
- #block[$ ⟦Γ ⊢ elim_TT⟧sg = &α ↦ β ↦ C ↦ red(
    (h_1 ∈ notred(C(red(•)))) ↦ \
    &(h_2 ∈
      scripts(product)_(a ∈ notred(α))
      scripts(product)_(b : notred(β(red(a))) → notred(TL_(a ∈ α) β(a)))
      scripts(product)_(h ∈
        product_(i ∈ notred(β(red(a)))) notred(C(red(b(i)))))
      notred(C(red((a, b))))
    ) ↦ \
    &(t ∈ notred(TL_(a ∈ α) β(a))) ↦
    ι(x(notred(φ(α, β, C, red(h_1), (a, b, h) ↦
      red(h_2(notred(a), notred(b), notred(h))), red(t), red(x)))))
  ) $]
  where #block[$
    φ(α, β, C, h_1, h_2, x, y) = & red(∀ A ⊆
      scripts(sum)_(t ∈ notred(T_(a ∈ α) β(a))) notred(C(red(t)))\,
      (•, notred(h_1)) ∈ A ∧ \ & [∀
        (a ∈ notred(α))
        (b : notred(β(red(a))) → notred(TL_(a ∈ α) β(a)))
        (h ∈ scripts(product)_(i ∈ notred(β(red(a))))
          notred(C(red(b(i))))), \ &
        (∀ i ∈ notred(β(red(a))), (b(i), h(i)) ∈ A) ⇒
        ((a, b), notred(h_2(red(a), red(b), red(h)))) ∈ A
        ] ⇒ (notred(x), notred(y)) ∈ A
    ) $]
- $⟦Γ ⊢ elimnode⟧sg = α ↦ β ↦ C ↦ red(h_1 ↦ h_2 ↦ •)$
- $⟦Γ ⊢ elimbranch⟧sg = α ↦ β ↦ C ↦ red(h_1 ↦ h_2 ↦
    (a ∈ α) ↦
    (b : notred(β(red(a))) → notred(TL_(a ∈ α) β(a))) ↦
    •
    )$
- $⟦Γ ⊢ lelim_TT⟧sg = α ↦ β ↦ h_1 ↦ h_2 ↦ red((t ∈ notred(TL_(a ∈ α) β(a))) ↦
  ι(x(notred(φ(α, β, i ↦ V_λ, h_1, h_2, red(t), red(x)))))
  )$

module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.RelativeExtensionEndpointWitness

/-!
概要：底・初期値・終点の底の厳密な表示変更を、元の指定終点比較へ値を変えずに渡す。
方針：同じ実延長・実終点を保持する証拠の等式へ戻し、指定比較の定義を保つ。
規約：比較を選び直さない。使われ方：元の指定三角形比較と長辺三証拠の比較の同定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の実延長・実終点を変えず、底・初期値・終点の底の表示だけを同じ等式で移す。 -/
def RelativeExtensionEndpointWitness.transportData
    {A D C E F B : SSet.{u}} {p : E ⟶ B} {b b' : A ⟶ B} {i : D ⟶ A}
    {v v' : D ⟶ E} {j : C ⟶ A} {q : F ⟶ B} {a a' : C ⟶ F}
    (w : RelativeExtensionEndpointWitness p b i v j q a)
    (hb : b = b') (hv : v = v') (ha : a = a') :
    RelativeExtensionEndpointWitness p b' i v' j q a' where
  extension := w.extension
  over := w.over.trans hb
  initial := w.initial.trans hv
  endpoint := w.endpoint
  endpoint_over := w.endpoint_over.trans ha
  evaluate := w.evaluate

/-- 実証拠の初期面と射影から、同じ底と全初期値の可換性を回収する。 -/
lemma RelativeExtensionEndpointWitness.initial_base
    {A D C E F B : SSet.{u}} {p : E ⟶ B} {b : A ⟶ B} {i : D ⟶ A} {v : D ⟶ E}
    {j : C ⟶ A} {q : F ⟶ B} {a : C ⟶ F}
    (w : RelativeExtensionEndpointWitness p b i v j q a) : v ≫ p = i ≫ b := by
  rw [← w.initial, Category.assoc, w.over]

/-- 同じ実終点の二射影から、元の底の終点の可換性を回収する。 -/
lemma RelativeExtensionEndpointWitness.endpoint_base
    {A D C E F B : SSet.{u}} {p : E ⟶ B} {b : A ⟶ B} {i : D ⟶ A} {v : D ⟶ E}
    {j : C ⟶ A} {q : F ⟶ B} {a : C ⟶ F}
    (w : RelativeExtensionEndpointWitness p b i v j q a) : j ≫ b = a ≫ q := by
  rw [← w.over, ← Category.assoc, w.evaluate, Category.assoc, pullback.condition,
    ← Category.assoc, w.endpoint_over]

/-- 実延長と実終点が同じなら、同じ底と初期値を保つ全証拠は厳密に等しい。 -/
lemma RelativeExtensionEndpointWitness.eq_of_extension_endpoint
    {A D C E F B : SSet.{u}} {p : E ⟶ B} {b : A ⟶ B} {i : D ⟶ A} {v : D ⟶ E}
    {j : C ⟶ A} {q : F ⟶ B} {a : C ⟶ F}
    (w w' : RelativeExtensionEndpointWitness p b i v j q a)
    (he : w.extension = w'.extension) (hg : w.endpoint = w'.endpoint) : w = w' := by
  cases w
  cases w'
  dsimp only at he hg
  cases he
  cases hg
  rfl

/-- 同じ実延長・実終点を保つ底と初期値の表示変更は、元の指定比較を値まで保つ。 -/
lemma RelativeExtensionEndpointWitness.iso_heq_of_dataEq
    {A D C E F B : SSet.{u}} {p : E ⟶ B} [LeftFibration p]
    {b b' : A ⟶ B} {i : D ⟶ A} {v v' : D ⟶ E} {j : C ⟶ A}
    {q : F ⟶ B} {a a' : C ⟶ F}
    (w₀ w₁ : RelativeExtensionEndpointWitness p b i v j q a)
    (w₀' w₁' : RelativeExtensionEndpointWitness p b' i v' j q a')
    (hb : b = b') (hv : v = v') (ha : a = a')
    (he₀ : w₀.extension = w₀'.extension) (he₁ : w₁.extension = w₁'.extension)
    (hg₀ : w₀.endpoint = w₀'.endpoint) (hg₁ : w₁.endpoint = w₁'.endpoint)
    (hi : leftAnodyneExtensions i) (hvb : v ≫ p = i ≫ b) (hvb' : v' ≫ p = i ≫ b')
    (hjb : j ≫ b = a ≫ q) (hjb' : j ≫ b' = a' ≫ q) :
    HEq (w₀.iso w₁ hi hvb hjb) (w₀'.iso w₁' hi hvb' hjb') := by
  subst b'
  subst v'
  subst a'
  have hw₀ := w₀.eq_of_extension_endpoint w₀' he₀ hg₀
  have hw₁ := w₁.eq_of_extension_endpoint w₁' he₁ hg₁
  subst w₀'
  subst w₁'
  rfl

end SerrePositivity.InfinityCategories.F2

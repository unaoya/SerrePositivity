module

public import SerrePositivity.CommutativeAlgebra.LocalAlgebraDiagram
public import Mathlib.Logic.Function.Basic

/-! # 図式の一段と構造を保つ写像の移送

履歴の制限一致から得られる等式で、環・代数の構造も含めて写像を移す。
環の台だけの等式による移送は使わない。
-/

@[expose] public section
namespace SerrePositivity
universe u v
variable {B K : Type u} [CommRing B] [CommRing K] [Algebra B K]

/-- 指定終域への写像を持つ局所B代数の一段。 -/
structure LocalAlgebraPoint where
  carrier : Type u
  [ring : CommRing carrier]
  [localRing : IsLocalRing carrier]
  [algebra : Algebra B carrier]
  [baseLocal : IsLocalHom (algebraMap B carrier)]
  target : carrier →ₐ[B] K

attribute [instance] LocalAlgebraPoint.ring LocalAlgebraPoint.localRing
  LocalAlgebraPoint.algebra LocalAlgebraPoint.baseLocal

/-- 図式から構造と指定終域を含む一段を取り出す。 -/
def LocalAlgebraDiagram.point {ι : Type v} [Preorder ι]
    (D : LocalAlgebraDiagram B K ι) (i : ι) : LocalAlgebraPoint (B := B) (K := K) where
  carrier := D.obj i
  target := D.target i

theorem LocalAlgebraDiagram.point_reindex {ι κ : Type v} [Preorder ι] [Preorder κ]
    (D : LocalAlgebraDiagram B K ι) (r : κ → ι) (hr : Monotone r) (i : κ) :
    (D.reindex r hr).point i = D.point (r i) := rfl

/-- 制限した図式の等式は、遷移写像の型と構造を含む一致を与える。 -/
theorem LocalAlgebraDiagram.map_heq_of_reindex_eq {ι κ : Type v} [Preorder ι] [Preorder κ]
    (D : LocalAlgebraDiagram B K ι) (E : LocalAlgebraDiagram B K κ)
    (r : κ → ι) (hr : Monotone r) (hDE : D.reindex r hr = E)
    (j k : κ) (h : j ≤ k) : HEq (D.map (r j) (r k) (hr h)) (E.map j k h) := by
  cases hDE
  rfl

/-- 源と終域の段の等式に沿って代数写像を移す。 -/
def LocalAlgebraPoint.castMap {A A' C C' : LocalAlgebraPoint (B := B) (K := K)}
    (hA : A = A') (hC : C = C') (f : A.carrier →ₐ[B] C.carrier) :
    A'.carrier →ₐ[B] C'.carrier := by
  cases hA
  cases hC
  exact f

theorem LocalAlgebraPoint.castMap_heq {A A' C C' : LocalAlgebraPoint (B := B) (K := K)}
    (hA : A = A') (hC : C = C') (f : A.carrier →ₐ[B] C.carrier) :
    HEq (LocalAlgebraPoint.castMap hA hC f) f := by
  cases hA
  cases hC
  rfl

theorem LocalAlgebraPoint.ring_heq {A C : LocalAlgebraPoint (B := B) (K := K)}
    (h : A = C) : HEq A.ring C.ring := by cases h; rfl

theorem LocalAlgebraPoint.algebra_heq {A C : LocalAlgebraPoint (B := B) (K := K)}
    (h : A = C) : HEq A.algebra C.algebra := by cases h; rfl

theorem LocalAlgebraPoint.target_heq {A C : LocalAlgebraPoint (B := B) (K := K)}
    (h : A = C) : HEq A.target C.target := by cases h; rfl

/-- 一段ごとの一致と遷移の一致から、図式全体の等式を得る。 -/
theorem LocalAlgebraDiagram.ext_point {ι : Type v} [Preorder ι]
    (D E : LocalAlgebraDiagram B K ι)
    (hp : ∀ i, D.point i = E.point i)
    (hm : ∀ j k h, HEq (D.map j k h) (E.map j k h)) : D = E := by
  apply LocalAlgebraDiagram.ext
  · funext i
    exact congrArg LocalAlgebraPoint.carrier (hp i)
  · apply Function.hfunext rfl
    intro i j hij
    cases eq_of_heq hij
    exact LocalAlgebraPoint.ring_heq (hp i)
  · apply Function.hfunext rfl
    intro i j hij
    cases eq_of_heq hij
    exact LocalAlgebraPoint.algebra_heq (hp i)
  · apply Function.hfunext rfl
    intro j j' hj
    cases eq_of_heq hj
    apply Function.hfunext rfl
    intro k k' hk
    cases eq_of_heq hk
    apply Function.hfunext rfl
    intro h h' hh
    exact hm j k h
  · apply Function.hfunext rfl
    intro i j hij
    cases eq_of_heq hij
    exact LocalAlgebraPoint.target_heq (hp i)

end SerrePositivity

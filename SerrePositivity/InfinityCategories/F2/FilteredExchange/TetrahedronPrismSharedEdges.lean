module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedFixedFaceFamily
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitUnitPointedZeroFaceSection

/-!
概要：全係数付き実三単体の二面で共有する辺の prism を厳密に同定する。
方針：結合子で元の全三単体へ戻し、元の二つの面の合成の等式を使う。
規約：全パラメータと実持ち上げを保持。使われ方：四面の指定辺比較を同じ六比較へ揃える。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E K Q : SSet.{u}} (U : ((Δ[3] : SSet.{u}) ⊗ E) ⊗ K ⟶ Q)

/-- 元の全係数付き実三単体の面を、同じ結合子で全係数の二単体 prism として表示する。 -/
def tetrahedronPrismFace (j : Fin 4) : (Δ[2] : SSet.{u}) ⊗ (E ⊗ K) ⟶ Q :=
  (α_ Δ[2] E K).inv ≫ ((stdSimplex.δ j ▷ E) ▷ K) ≫ U

/-- 同じ実二面の辺は、元の全三単体の二つの面の合成に厳密に因子分解する。 -/
lemma tetrahedronPrismFace_edge (i : Fin 3) (j : Fin 4) :
    (stdSimplex.δ i ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U j =
      ((stdSimplex.δ i ≫ stdSimplex.δ j) ▷ (E ⊗ K)) ≫ (α_ Δ[3] E K).inv ≫ U := by
  unfold tetrahedronPrismFace
  have h : (stdSimplex.δ i ▷ (E ⊗ K)) ≫ (α_ Δ[2] E K).inv ≫
      ((stdSimplex.δ j ▷ E) ▷ K) =
      ((stdSimplex.δ i ≫ stdSimplex.δ j) ▷ (E ⊗ K)) ≫ (α_ Δ[3] E K).inv := by
    apply SSet.hom_ext
    intro n
    rfl
  simpa only [Category.assoc] using congrArg (fun f => f ≫ U) h

/-- 二面での同じ共有辺は、全係数と元の実三単体を保って厳密に一致する。 -/
lemma tetrahedronPrismFace_shared_edge {i i' : Fin 3} {j j' : Fin 4}
    (h : (stdSimplex.δ i : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫ stdSimplex.δ j =
      stdSimplex.δ i' ≫ stdSimplex.δ j') :
    (stdSimplex.δ i ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U j =
      (stdSimplex.δ i' ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U j' := by
  rw [tetrahedronPrismFace_edge, tetrahedronPrismFace_edge, h]

end SerrePositivity.InfinityCategories.F2

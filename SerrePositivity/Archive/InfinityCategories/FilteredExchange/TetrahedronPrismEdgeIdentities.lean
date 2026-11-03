module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.TetrahedronPrismSharedEdges

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

/-- 元の全実三単体の共有辺 01 は、二面の実制限として厳密に一致する。 -/
lemma tetrahedronPrismSharedEdge01 :
    (stdSimplex.δ (2 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 2 =
      (stdSimplex.δ (2 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 3 :=
  tetrahedronPrismFace_shared_edge U (stdSimplex.δ_comp_δ_self (i := (2 : Fin 3)))

/-- 元の全実三単体の共有辺 02 は、二面の実制限として厳密に一致する。 -/
lemma tetrahedronPrismSharedEdge02 :
    (stdSimplex.δ (2 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 1 =
      (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 3 :=
  tetrahedronPrismFace_shared_edge U ((stdSimplex.δ_comp_δ (show (1 : Fin 3) ≤ 2 by decide)).symm)

/-- 元の全実三単体の共有辺 03 は、二面の実制限として厳密に一致する。 -/
lemma tetrahedronPrismSharedEdge03 :
    (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 1 =
      (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 2 :=
  tetrahedronPrismFace_shared_edge U (stdSimplex.δ_comp_δ_self (i := (1 : Fin 3)))

/-- 元の全実三単体の共有辺 12 は、二面の実制限として厳密に一致する。 -/
lemma tetrahedronPrismSharedEdge12 :
    (stdSimplex.δ (0 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 3 =
      (stdSimplex.δ (2 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 0 := by
  apply tetrahedronPrismFace_shared_edge U
  simpa only [Fin.castSucc_zero, show Fin.succ (2 : Fin 3) = (3 : Fin 4) by decide] using
    (stdSimplex.δ_comp_δ (show (0 : Fin 3) ≤ 2 by decide))

/-- 元の全実三単体の共有辺 13 は、二面の実制限として厳密に一致する。 -/
lemma tetrahedronPrismSharedEdge13 :
    (stdSimplex.δ (0 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 2 =
      (stdSimplex.δ (1 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 0 := by
  apply tetrahedronPrismFace_shared_edge U
  simpa only [Fin.castSucc_zero, show Fin.succ (1 : Fin 3) = (2 : Fin 4) by decide] using
    (stdSimplex.δ_comp_δ (show (0 : Fin 3) ≤ 1 by decide))

/-- 元の全実三単体の共有辺 23 は、二面の実制限として厳密に一致する。 -/
lemma tetrahedronPrismSharedEdge23 :
    (stdSimplex.δ (0 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 1 =
      (stdSimplex.δ (0 : Fin 3) ▷ (E ⊗ K)) ≫ tetrahedronPrismFace U 0 :=
  tetrahedronPrismFace_shared_edge U ((stdSimplex.δ_comp_δ_self (i := (0 : Fin 3))).symm)

end SerrePositivity.InfinityCategories.F2

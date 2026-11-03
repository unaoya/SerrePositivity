module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedSectionPointFiberIso

/-!
概要：辺の共通終点への底上制限と点上切断の表示同型を、元の終点 fiber 評価へ同定する。
方針：同じ点評価の pointed 座標を比較し、明示した元の小さい fiber の包含で射を比較する。
規約：頂点等式と底上の可換性を入力に保持。使われ方：切断 cospan の共通標的の表示変更。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 共通点への制限と表示同型の合成は、元の同じ終点の小さい fiber への評価である。 -/
lemma pointedSectionTargetFiber_eq_point_iso {B : SSet.{u}}
    (J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) (b : B _⦋0⦌)
    (a : (Δ[0] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
    (ha : a.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 0) = J.app _ (ULift.up b))
    (e : (Δ[1] : SSet.{u + 1}) ⟶ SpaceInfinity.{u})
    (he : e.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm 1) = J.app _ (ULift.up b))
    (hj : stdSimplex.δ (0 : Fin 2) ≫ e = a) :
    relativeFunctorOverPre pointedSpaceProjection
      (Over.homMk (U := Over.mk a) (V := Over.mk e) (stdSimplex.δ (0 : Fin 2)) hj) ≫
        (pointedSectionPointFiberIso J b a ha).hom = pointedSectionTargetFiber J b e he := by
  have h := pointedSectionTargetFiber_eq_of_evaluate_ι J b e he
    (𝟙 (relativeFunctorSpace pointedSpaceProjection e))
    (relativeFunctorOverPre pointedSpaceProjection
      (Over.homMk (U := Over.mk a) (V := Over.mk e) (stdSimplex.δ (0 : Fin 2)) hj) ≫
        (pointedSectionPointFiberIso J b a ha).hom) (by
      rw [Category.id_comp, Category.assoc, pointedSectionPointFiberIso_pointed]
      exact (relativeFunctorOverPre_point_ι pointedSpaceProjection a e
        (stdSimplex.δ (0 : Fin 2)) hj).symm)
  simpa only [Category.id_comp] using h.symm

end SerrePositivity.InfinityCategories.F2

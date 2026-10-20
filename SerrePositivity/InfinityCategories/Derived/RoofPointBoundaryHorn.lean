module
public import SerrePositivity.InfinityCategories.Derived.RoofPointSliceSimplexInverse
public import SerrePositivity.InfinityCategories.Core.TerminalUniqueness

/-! # 任意次元の実 over 境界からの元の最後ホーン

概要：over への実境界写像を、既存の境界 join 同型により元の実最後ホーンへ移す。
方針：各境界面の join を同じ番号の指定ホーン面へ同定し、uncurry の自然性を使う。
規約：全境界写像を入力する。使われ方：有限図式の高次境界を実 Hom 残差へ渡す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
open scoped Simplicial
variable {X : SSet.{u}} (a : Δ[0] ⟶ X)

/-- 各境界面の join は、元の最後ホーンの同じ番号の指定面である。 -/
lemma roofPointBoundaryFaceJoin {n : ℕ} (j : Fin (n + 2)) :
    (joinStdSimplexIso n 0).inv ≫ joinMap (boundary.ι j) (𝟙 Δ[0]) ≫
        (finalHornPointJoinIso.{u} (n + 1)).hom =
      horn.ι (Fin.last (n + 2)) j.castSucc (Fin.castSucc_ne_last j) := by
  apply (cancel_mono (horn (n + 2) (Fin.last (n + 2))).ι).mp
  calc
    _ = (joinStdSimplexIso n 0).inv ≫
        joinMap (SSet.stdSimplex.δ j) (𝟙 Δ[0]) ≫ (joinStdSimplexIso (n + 1) 0).hom := by
      simp only [Category.assoc, finalHornPointJoinIso_hom_ι]
      rw [← Category.assoc (joinMap _ _) (joinMap _ _), ← joinMap_comp,
        boundary.ι_ι, Category.id_comp]
    _ = SSet.stdSimplex.δ j.castSucc := by
      have hi : joinMap (SSet.stdSimplex.δ j) (𝟙 Δ[0]) ≫
          (joinStdSimplexIso (n + 1) 0).hom =
          (joinStdSimplexIso n 0).hom ≫ SSet.stdSimplex.δ j.castSucc :=
        (joinStdSimplexIso_rightPoint_naturality (SimplexCategory.δ j)).trans
          (congrArg (fun f => (joinStdSimplexIso n 0).hom ≫ SSet.stdSimplex.map f)
            (roofPointExtend_coface j))
      rw [hi, Iso.inv_hom_id_assoc]
    _ = _ := (horn.ι_ι (Fin.last (n + 2)) j.castSucc (Fin.castSucc_ne_last j)).symm

/-- 実 over 境界の uncurry を、既存の最後ホーン同型で戻した実ホーン。 -/
def roofPointBoundaryHorn {n : ℕ} (B : (∂Δ[n + 1] : SSet.{u}) ⟶ sliceOver a) :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) ⟶ X :=
  (finalHornPointJoinIso (n + 1)).inv ≫ sliceOverUncurry B

/-- この実ホーンの各指定面は、元の同じ over 境界面の回収単体である。 -/
lemma roofPointBoundaryHorn_face {n : ℕ} (B : (∂Δ[n + 1] : SSet.{u}) ⟶ sliceOver a)
    (j : Fin (n + 2)) :
    horn.ι (Fin.last (n + 2)) j.castSucc (Fin.castSucc_ne_last j) ≫ roofPointBoundaryHorn a B =
      roofPointSliceSimplex a (SSet.yonedaEquiv (boundary.ι j ≫ B)) := by
  rw [← roofPointBoundaryFaceJoin, roofPointBoundaryHorn]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← sliceOverUncurry_precomp]
  have he := sliceOverUncurry_yoneda n (SSet.yonedaEquiv (boundary.ι j ≫ B))
  simp only [Equiv.symm_apply_apply] at he
  exact congrArg ((joinStdSimplexIso n 0).inv ≫ ·) he

/-- 最終頂点に接するホーンの最後辺は、元の同じ境界頂点の構造辺である。 -/
lemma roofPointBoundaryHorn_lastEdge {n : ℕ} (B : (∂Δ[n + 1] : SSet.{u}) ⟶ sliceOver a) :
    (roofPointBoundaryHorn a B).app _ (finalHornEdge n) =
      SSet.yonedaEquiv (roofPointSliceSimplex a (SSet.yonedaEquiv
        (boundaryVertex n (Fin.last (n + 1)) ≫ B))) := by
  rw [← finalHornPointJoinIso_edge, ← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv (((joinStdSimplexIso 0 0).inv ≫
    joinMap (boundaryVertex n (Fin.last (n + 1))) (𝟙 Δ[0]) ≫
      (finalHornPointJoinIso (n + 1)).hom) ≫
        ((finalHornPointJoinIso (n + 1)).inv ≫ sliceOverUncurry B)) = _
  rw [Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, ← sliceOverUncurry_precomp]
  have he := sliceOverUncurry_yoneda 0
    (SSet.yonedaEquiv (boundaryVertex n (Fin.last (n + 1)) ≫ B))
  simp only [Equiv.symm_apply_apply] at he
  exact congrArg (fun f => SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫ f)) he

end SerrePositivity.InfinityCategories

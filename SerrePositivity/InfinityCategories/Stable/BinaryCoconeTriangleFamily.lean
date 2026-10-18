module
public import SerrePositivity.InfinityCategories.Stable.CoconeLegTriangle
public import SerrePositivity.InfinityCategories.Stable.BinaryCoconeEdges

/-! # 二つの脚の合成二単体の貼り合わせ

概要：離散二点図式の二つの脚の合成二単体を一つの余錐の族にする。
方針：共通の頂点の辺に沿う join の pushout を使う。
規約：端点の余錐と指定した辺を厳密に保つ。使われ方：余積の射の一意性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：二つの合成二単体から、元と先を保つ二点図式の余錐の族が得られる。
方針：二つの点と区間の join を共通区間に沿って貼り、制限を計算する。
規約：値域に quasicategory 性を仮定しない。使われ方：coslice の辺の構成。 -/
lemma exists_binaryCoconeTriangleFamily {X : SSet.{u}}
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} {c d : JoinCocone p}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex d.vertex}
    (L : (c.leg binaryPointLeft).CompStruct e (d.leg binaryPointLeft))
    (R : (c.leg binaryPointRight).CompStruct e (d.leg binaryPointRight)) :
    ∃ U : join ((Δ[0] : SSet.{u}) ⨿ Δ[0]) Δ[1] ⟶ X,
      joinInl _ _ ≫ U = p ∧
      joinMap (𝟙 _) (stdSimplex.δ (1 : Fin 2)) ≫ U = c.val ∧
      joinMap (𝟙 _) (stdSimplex.δ (0 : Fin 2)) ≫ U = d.val ∧
      joinInr _ _ ≫ U = SSet.yonedaEquiv.symm e.edge := by
  let P := join_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[1]
  let U := P.desc (coconeLegTriangle L) (coconeLegTriangle R)
    ((coconeLegTriangle_right L).trans (coconeLegTriangle_right R).symm)
  have hL : joinMap binaryPointLeft (𝟙 (Δ[1] : SSet.{u})) ≫ U =
      coconeLegTriangle L := P.inl_desc _ _ _
  have hR : joinMap binaryPointRight (𝟙 (Δ[1] : SSet.{u})) ≫ U =
      coconeLegTriangle R := P.inr_desc _ _ _
  have hrestrict (i : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0])
      (j : Fin 2) :
      joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫
          joinMap (𝟙 _) (stdSimplex.δ j) =
        joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ j) ≫ joinMap i (𝟙 Δ[1]) := by
    rw [← joinMap_comp, ← joinMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · apply coprod.hom_ext
    · rw [← Category.assoc binaryPointLeft,
        ← joinInl_joinMap binaryPointLeft (𝟙 (Δ[1] : SSet.{u})), Category.assoc,
        hL, coconeLegTriangle_fixed]
    · rw [← Category.assoc binaryPointRight,
        ← joinInl_joinMap binaryPointRight (𝟙 (Δ[1] : SSet.{u})), Category.assoc,
        hR, coconeLegTriangle_fixed]
  · apply (join_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[0]).hom_ext
    · rw [← Category.assoc, hrestrict, Category.assoc, hL, coconeLegTriangle_zero]
    · rw [← Category.assoc, hrestrict, Category.assoc, hR, coconeLegTriangle_zero]
  · apply (join_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[0]).hom_ext
    · rw [← Category.assoc, hrestrict, Category.assoc, hL, coconeLegTriangle_one]
    · rw [← Category.assoc, hrestrict, Category.assoc, hR, coconeLegTriangle_one]
  · have h := congrArg (fun a => joinInr (Δ[0] : SSet.{u}) Δ[1] ≫ a) hL
    rw [← Category.assoc, joinInr_joinMap, Category.id_comp,
      coconeLegTriangle_right] at h
    exact h

end SerrePositivity.InfinityCategories

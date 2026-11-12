module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoconeLegTriangle
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoconeEdges

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：二つの合成二単体から、元と先を保つ二点図式の余錐の族が得られる。
方針：二つの点と区間の join を共通区間に沿って貼り、制限を計算する。
規約：値域に quasicategory 性を仮定しない。使われ方：coslice の辺の構成。 -/
lemma exists_binaryCoconeTriangleFamily {X : SSet.{u}}
    {p : (Δ[0] : SSet.{u}) ⨿ Δ[0] ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex d.vertex}
    (L : (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft).CompStruct e (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft))
    (R : (c.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight).CompStruct e (d.leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight)) :
    ∃ U : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((Δ[0] : SSet.{u}) ⨿ Δ[0]) Δ[1] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ U = p ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (stdSimplex.δ (1 : Fin 2)) ≫ U = c.val ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (stdSimplex.δ (0 : Fin 2)) ≫ U = d.val ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ U = SSet.yonedaEquiv.symm e.edge := by
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[1]
  let U := P.desc (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle L) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle R)
    ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle_right L).trans (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle_right R).symm)
  have hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft (𝟙 (Δ[1] : SSet.{u})) ≫ U =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle L := P.inl_desc _ _ _
  have hR : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight (𝟙 (Δ[1] : SSet.{u})) ≫ U =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle R := P.inr_desc _ _ _
  have hrestrict (i : (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ Δ[0])
      (j : Fin 2) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) (stdSimplex.δ j) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[1]) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
    simp only [Category.id_comp, Category.comp_id]
  refine ⟨U, ?_, ?_, ?_, ?_⟩
  · apply coprod.hom_ext
    · rw [← Category.assoc _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft,
        ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft (𝟙 (Δ[1] : SSet.{u})), Category.assoc,
        hL, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle_fixed]
    · rw [← Category.assoc _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight,
        ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight (𝟙 (Δ[1] : SSet.{u})), Category.assoc,
        hR, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle_fixed]
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[0]).hom_ext
    · rw [← Category.assoc, hrestrict, Category.assoc, hL, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle_zero]
    · rw [← Category.assoc, hrestrict, Category.assoc, hR, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle_zero]
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_coproduct_isPushout (Δ[0] : SSet.{u}) Δ[0] Δ[0]).hom_ext
    · rw [← Category.assoc, hrestrict, Category.assoc, hL, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle_one]
    · rw [← Category.assoc, hrestrict, Category.assoc, hR, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle_one]
  · have h := congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[1] ≫ a) hL
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.id_comp,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeLegTriangle_right] at h
    exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

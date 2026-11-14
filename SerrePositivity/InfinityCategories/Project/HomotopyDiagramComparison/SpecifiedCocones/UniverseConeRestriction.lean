module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.FiniteShapes.FiniteProductPreservation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.ConeValEquality
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorVertexConeReindex

/-!
概要：形状制限と宇宙変更による全錐の比較。
方針：join の宇宙比較の自然性で元の全射を比較する。
規約：指定錐と元の形状写像を保持する。
使われ方：有限積錐の同型形状への保存の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：錐形状の宇宙比較は右因子の全射に自然。
方針：join 宇宙同型の自然性と標準単体の宇宙同型を合成する。
規約：元の形状写像を保持する。
使われ方：同じ全錐の制限と宇宙変更の交換。 -/
lemma uliftConeShapeIso_inv_rightMap {K L : SSet.{u}} (f : L ⟶ K) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[n] : SSet.{max u v})) ((SSet.uliftFunctor.{v, u}).map f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, v} K n).inv =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso.{u, v} L n).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[n] : SSet.{u})) f) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_inv_naturality.{u, v} (𝟙 (Δ[n] : SSet.{u})) f
  rw [(SSet.uliftFunctor.{v, u}).map_id] at h
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso, Iso.trans_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, Iso.refl_inv]
  rw [Category.assoc, ← h]
  simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]

/-- 概要：錐の制限と持ち上げは同じ全射を与える。
方針：錐形状の自然性を元の全錐射へ後合成する。
規約：元の頂点と全脚を保持する。
使われ方：同型形状による全極限錐の宇宙変更。 -/
lemma ulift_restrictJoinCone_val {K L X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (f : L ⟶ K) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, v} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c f)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, v} c)
        ((SSet.uliftFunctor.{v, u}).map f)).val := by
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso L 0).inv ≫
      (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) f ≫ c.val) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) ((SSet.uliftFunctor.{v, u}).map f) ≫
      ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftConeShapeIso K 0).inv ≫ (SSet.uliftFunctor.{v, u}).map c.val)
  rw [Functor.map_comp, ← Category.assoc, ← uliftConeShapeIso_inv_rightMap, Category.assoc]

/-- 概要：有限積保存は有限離散 nerve と同型な形状上の全錐にも適用できる。
方針：小さい形状で制限し、保存後に同じ持ち上げ同型で極限性を戻す。
規約：同型と元の全錐を明示する。
使われ方：有限余積の反転形状の有限積保存。 -/
lemma PreservesFiniteProductsFromSmallSource.map_isLimit_of_shapeIso
    {C : SSet.{u}} {X : SSet.{u + 1}}
    {F : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ X}
    (hF : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PreservesFiniteProductsFromSmallSource F)
    {J : Type u} [Finite J] {K : SSet.{u}} (e : nerve (Discrete J) ≅ K)
    {p : K ⟶ C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c)) := by
  have hs := hF J (e.hom ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c e.hom)
    ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_restrict_iff_of_isIso c e.hom).mpr hc)
  have hv : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c e.hom))).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone F (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c))
        ((SSet.uliftFunctor.{u + 1, u}).map e.hom)).val := by
    change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c e.hom)).val ≫ F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 1, u}).map e.hom) ≫
        ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).val ≫ F)
    rw [ulift_restrictJoinCone_val]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 1, u}).map e.hom) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u, u + 1} c).val) ≫ F = _
    rw [Category.assoc]
  exact (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_restrict_iff_of_isIso _ _).mp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isLimitCone_iff_of_cone_val_eq _ _ hv).mp hs)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

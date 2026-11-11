module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SourceCosliceRestrictedColimit

/-!
概要：固定始域へ制限した全余錐の頂点は、元の余錐の同じ始域への制限そのもの。
方針：反復 coslice 同型の左因子制限を計算する。
規約：頂点同型だけでなく元の構造射の厳密な等式を返す。
使われ方：指定表示段を保った compact 因子化の終点の同定。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：制限した余錐の頂点は元の固定始域からの同じ射。
方針：反復 coslice の左制限と元の余錐値への二度の制限を計算する。
規約：元の余錐の全構造射を厳密に保つ。
使われ方：coslice 内の恒等辺の compact 因子化。 -/
lemma sourceCosliceRestrictedCocone_vertex {K A I C : SSet.{u}}
    (a : K ⟶ I) (s : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) (D : I ⟶ C) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone a s D c).vertex = c.restrict a := by
  let b := s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a D
  have hU : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry s ≫ D :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_postcomp s D
  let d : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b)) _⦋0⦌ :=
    (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hU.symm)).hom.app (Opposite.op ⦋0⦌)
      (c.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry s))
  have hp : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso b).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uncurriedSliceUnderRestriction b := by
    rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso_restriction b, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]
  change ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.iteratedSliceUnderIso b).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection b).app
    (Opposite.op ⦋0⦌) d = c.restrict a
  rw [hp]
  apply Subtype.ext
  change ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed b))).hom.app
    (Opposite.op ⦋0⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A)).app
      (Opposite.op ⦋0⦌) d)).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnder_eqToIso_val (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed b)]
  have hd : d.val = (c.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry s)).val :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnder_eqToIso_val hU.symm _
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A) (𝟙 Δ[0]) ≫ d.val = _
  rw [hd]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K A) (𝟙 Δ[0]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry s) (𝟙 Δ[0]) ≫ c.val) = _
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

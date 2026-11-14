module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.NativeKanColimitTransfer
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.NativeCoconePreservationTransport

/-!
概要：元の余極限と同じ像の余極限を、両側の native 余錐制限で同時に輸送する。
方針：制限の本質全射性で全余錐を持ち上げ、両側の始対象性を反映する。
規約：像の頂点だけでなく、元の全余錐の保存を要求する。
使われ方：I-2 d′ の有限形状帰納における保存性の述語。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 同じ元の全余錐と、その元の関手による像がともに余極限であること。 -/
def HasPreservedColimit {K X Y : SSet.{u}} (G : X ⟶ Y) (p : K ⟶ X) : Prop :=
  ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c)

/-- 両側の native 制限同値は、元の全余錐の保存を伴う存在を保ち反映する。 -/
lemma hasPreservedColimit_iff_nativeRestriction
    {A K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    (p : K ⟶ X) (i : A ⟶ K) (G : X ⟶ Y)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i))
    (hiG : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (p ≫ G) i)) :
    HasPreservedColimit G p ↔ HasPreservedColimit G (i ≫ p) := by
  constructor
  · rintro ⟨c, hc, hGc⟩
    refine ⟨c.restrict i, (hi.choose.isInitialVertex_iff c).mp hc, ?_⟩
    have h := (hiG.choose.isInitialVertex_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c)).mp hGc
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c).restrict i) at h
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _).symm).mp h
  · rintro ⟨d, hd, hGd⟩
    obtain ⟨a₀, ⟨e⟩⟩ := hi.choose.isEssentiallySurjective d
    let a : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p := a₀
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (i ≫ p)) (a.restrict i) d := e
    have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone a := (hi.choose.isInitialVertex_iff a).mpr
      (hd.of_vertexIso he.symm)
    refine ⟨a, ha, ?_⟩
    have ht := hGd.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map he (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (i ≫ p) G)).symm
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G (a.restrict i)) at ht
    apply (hiG.choose.isInitialVertex_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G a)).mpr
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G a).restrict i)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ (Category.assoc _ _ _)).mp ht

/-- 一つの保存された余極限があれば、元の任意の余極限全余錐も同じ関手で保存。 -/
lemma HasPreservedColimit.map_isColimit {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {G : X ⟶ Y} {p : K ⟶ X}
    (h : HasPreservedColimit G p) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone G c) := by
  obtain ⟨d, hd, hGd⟩ := h
  exact hGd.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d c hd hc) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p G))

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.4.2.5" (partial := direction) "仮定：始対象と押し出しを保つ関手、始域の有限余極限（HTT の十分方向と一致。Lean では空図式と標準三頂点 span に保存される余極限を指定）。結論：任意の有限形状について余極限余錐の像は余極限（一致する方向。逆向きは含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit.map_isColimit
attribute [cite HTT "4.4.2.9" (partial := special) "仮定：左ファイブレーションと弱可縮な図式形状（Lean が強い：形状に終頂点がある場合。関手には左ファイブレーション性を要求しない）。結論：同じ余極限余錐の像が余極限となる（(1) の保存方向が一致する場合。反映と底の指定余錐の持ち上げ (2) は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit.map_isColimit

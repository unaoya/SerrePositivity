module

public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.TensorColimitConeExistence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-!
概要：余完備な二圏の直積の小余極限と、二射影による保存・検出を構成する。
方針：元の両成分の余錐を合わせ、他の余極限余錐は一意性の同型で比較する。
規約：accessibility や presentable 性は仮定せず、元の任意小形状を保持する。
使われ方：Pr^L の積に必要な余極限側の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {X Y : SSet.{u + 1}} [Quasicategory X] [Quasicategory Y]

/-- 概要：余完備な二圏の直積は全小余極限を持つ。
方針：両成分の元の余極限余錐を同じ直積余錐へ合わせる。
規約：任意の小さい単体集合形状を扱う。
使われ方：presentable の積の余完備性。 -/
lemma tensor_hasSmallColimits (hX : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X) (hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (X ⊗ Y) := by
  intro K D
  obtain ⟨cx, hx⟩ := hX K (D ≫ fst X Y)
  obtain ⟨cy, hy⟩ := hY K (D ≫ snd X Y)
  obtain ⟨c, hc, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.exists_colimitCone_tensor_with_components D cx cy hx hy
  exact ⟨c, hc⟩

/-- 概要：余完備な二圏の直積内の余極限性は元の二射影で検出される。
方針：両成分から構成した余極限余錐との同型を射影で写す。
規約：指定した元の全余錐を判定する。
使われ方：射影と直積への関手の全小余極限保存。 -/
lemma tensor_isColimitCone_iff_components (hX : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X)
    (hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y) {K : SSet.{u}}
    {D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ X ⊗ Y} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (fst X Y) c) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (snd X Y) c) := by
  have : Quasicategory (X ⊗ Y) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategory_tensor X Y
  constructor
  · intro hc
    obtain ⟨cx, hx⟩ := hX K (D ≫ fst X Y)
    obtain ⟨cy, hy⟩ := hY K (D ≫ snd X Y)
    obtain ⟨d, hd, hdx, hdy⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.exists_colimitCone_tensor_with_components D cx cy hx hy
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d c hd hc
    have hx' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (fst X Y) d) := hdx.symm ▸ hx
    have hy' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (snd X Y) d) := hdy.symm ▸ hy
    exact ⟨hx'.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp D (fst X Y))),
      hy'.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp D (snd X Y)))⟩
  · rintro ⟨hx, hy⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.isColimitCone_tensor_of_components c hx hy

/-- 概要：直積の第一射影は全小余極限を保存する。
方針：元の全余錐の成分判定の順方向を使う。
規約：小余極限の存在を両成分について明示する。
使われ方：Pr^L の積の射影。 -/
lemma tensor_fst_preservesSmallColimits (hX : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X)
    (hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (fst X Y) := by
  intro K D c hc
  exact ((tensor_isColimitCone_iff_components hX hY c).mp hc).1

/-- 概要：直積の第二射影は全小余極限を保存する。
方針：元の全余錐の成分判定の順方向を使う。
規約：小余極限の存在を両成分について明示する。
使われ方：Pr^L の積の射影。 -/
lemma tensor_snd_preservesSmallColimits (hX : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X)
    (hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (snd X Y) := by
  intro K D c hc
  exact ((tensor_isColimitCone_iff_components hX hY c).mp hc).2

/-- 概要：直積への関手の全小余極限保存は両成分の保存と同値。
方針：同じ元の全余錐の二つの像を成分判定に渡す。
規約：始域の余完備性は要求しない。
使われ方：Pr^L 内の積の普遍性。 -/
lemma tensor_preservesSmallColimits_iff_components {C : SSet.{u + 1}}
    (hX : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits X) (hY : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits Y) (F : C ⟶ X ⊗ Y) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits F ↔ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (F ≫ fst X Y) ∧
      _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (F ≫ snd X Y) := by
  constructor
  · intro hF
    constructor
    · intro K D c hc
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using
        ((tensor_isColimitCone_iff_components hX hY (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)).mp (hF K D c hc)).1
    · intro K D c hc
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using
        ((tensor_isColimitCone_iff_components hX hY (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)).mp (hF K D c hc)).2
  · rintro ⟨hx, hy⟩ K D c hc
    apply (tensor_isColimitCone_iff_components hX hY (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)).mpr
    constructor
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using hx K D c hc
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using hy K D c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

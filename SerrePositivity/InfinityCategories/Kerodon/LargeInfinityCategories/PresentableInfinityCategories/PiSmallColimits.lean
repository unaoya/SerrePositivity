module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PiColimitCones
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-!
概要：余完備な圏の小さい全直積の小余極限とその各成分計算。
方針：同じ形状の各余錐を組み合わせ、指定余錐の一意同型で各射影の保存性を示す。
規約：任意の小さい単体集合形状を扱う。
使われ方：小さい積の presentable 性と Pr^L の積の普遍性。

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

/-- 概要：元の各成分の指定余錐から直積内の全余錐を構成する。
方針：join からの元の全射をまとめる。
規約：同じ図式の成分を使う。使われ方：直積の余極限の存在。 -/
def piJoinCocone {ι : Type u} {C : ι → SSet.{u + 1}} {J : SSet.{u + 1}}
    {p : J ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C} (c : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetLift (fun i ↦ (c i).val), by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_hom_ext
    intro i
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetLift_projection] using (c i).property⟩

/-- 概要：組み合わせた余錐の指定成分は元の余錐。
方針：全射の各成分を評価する。
規約：余錐そのものの等式。使われ方：指定余錐の各成分の普遍性。 -/
lemma piJoinCocone_projection {ι : Type u} {C : ι → SSet.{u + 1}}
    {J : SSet.{u + 1}} {p : J ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C}
    (c : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)) (i : ι) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) (piJoinCocone c) = c i := by
  apply Subtype.ext
  rfl

/-- 概要：余完備な圏の小さい全直積は全小余極限を持つ。
方針：同じ小さい形状の各余極限を全直積へ組み合わせる。
規約：成分の accessibility を要求しない。
使われ方：小さい積の presentable 性の余完備性。 -/
lemma piSSet_hasSmallColimits {ι : Type u} {C : ι → SSet.{u + 1}}
    (hC : ∀ i, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (C i)) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) := by
  intro K p
  choose c hc using fun i ↦ hC i K (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)
  refine ⟨piJoinCocone c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isColimitCone_of_components _ ?_⟩
  intro i
  rw [piJoinCocone_projection]
  exact hc i

/-- 概要：余完備な圏の直積内の指定余錐の余極限性は全成分で判定される。
方針：成分から作る余極限との同型を各 coslice へ写す。
規約：元の指定余錐を保持する。
使われ方：各射影と直積への関手の保存性。 -/
lemma piSSet_isColimitCone_iff_components {ι : Type u} {C : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] (hC : ∀ i, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (C i))
    {K : SSet.{u}} {p : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) c) := by
  constructor
  · intro hc
    choose d hd using fun i ↦ hC i K (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)
    have hdi (i : ι) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) (piJoinCocone d)) := by
      rw [piJoinCocone_projection]
      exact hd i
    have hdp := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isColimitCone_of_components (piJoinCocone d) hdi
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso (piJoinCocone d) c hdp hc
    intro i
    exact (hdi i).of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i)))
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet_isColimitCone_of_components c

/-- 概要：余完備な圏の全直積の各射影は全小余極限を保つ。
方針：指定余錐の成分判定を使う。
規約：同じ元の射影。使われ方：Pr^L の小さい積の射影。 -/
lemma piSSetProjection_preservesSmallColimits {ι : Type u} {C : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] (hC : ∀ i, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (C i)) (i : ι) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) := by
  intro K p c hc
  exact ((piSSet_isColimitCone_iff_components hC c).mp hc) i

/-- 概要：全直積への関手の全小余極限保存は全成分の保存と同値。
方針：同じ元の全余錐の像に成分判定を適用する。
規約：始域の余完備性を要求しない。
使われ方：Pr^L の小さい積の普遍性。 -/
lemma piSSet_preservesSmallColimits_iff_components {ι : Type u} {C : ι → SSet.{u + 1}}
    [∀ i, Quasicategory (C i)] (hC : ∀ i, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (C i))
    {X : SSet.{u + 1}} (F : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSet C) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits F ↔ ∀ i, _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.piSSetProjection C i) := by
  constructor
  · intro hF i K p c hc
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using
      ((piSSet_isColimitCone_iff_components hC (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)).mp (hF K p c hc)) i
  · intro hF K p c hc
    apply (piSSet_isColimitCone_iff_components hC (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)).mpr
    intro i
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using hF i K p c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

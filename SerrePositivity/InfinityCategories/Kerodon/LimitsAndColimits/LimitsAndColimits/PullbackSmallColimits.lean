module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackColimitConeExistence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.InitialTransport

/-!
概要：余極限保存関手の引き戻しにおける全小余極限の構成と成分判定。
方針：一方の関手の同値持ち上げで像の余錐を厳密化し、両成分を貼り合わせる。
規約：同値持ち上げは明示入力。accessibility や presentable 性は結論しない。
使われ方：Pr^L の引き戻しの余完備性と普遍性への接続。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) (hqc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits q)

include hp hE hD hpc hqc

/-- 概要：余極限保存関手の引き戻しは全小余極限を持つ。
方針：元の両成分の余極限と像の保存性を公開された貼り合わせへ渡す。
規約：元の任意小図式を結論に保持する。
使われ方：Pr^L の引き戻しの余完備性。 -/
lemma pullback_hasSmallColimits : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (pullback p q) := by
  intro K r
  obtain ⟨ce, he⟩ := hE K (r ≫ pullback.fst p q)
  obtain ⟨cd, hd⟩ := hD K (r ≫ pullback.snd p q)
  obtain ⟨c, hc, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_pullback_with_snd p q hp r ce cd
    he (hpc K _ ce he) hd (hqc K _ cd hd)
  exact ⟨c, hc⟩

/-- 概要：引き戻し内の元の余錐の余極限性は両成分で判定される。
方針：成分から作った余極限との一意同型を両射影へ写す。
規約：同じ余錐を判定し、像の余極限保存を明示する。
使われ方：Pr^L の引き戻し射影と関手の保存判定。 -/
lemma pullback_isColimitCone_iff_components {K : SSet.{u}}
    {r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ pullback p q} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst p q) c) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.snd p q) c) := by
  have : InnerFibration p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.innerFibration hp
  have : InnerFibration (pullback.snd p q) :=
    ⟨innerFibrations.pullback_snd p q (InnerFibration.mem (q := p))⟩
  have : Quasicategory (pullback p q) := quasicategory_of_innerFibration (pullback.snd p q)
  constructor
  · intro hc
    obtain ⟨ce, he⟩ := hE K (r ≫ pullback.fst p q)
    obtain ⟨cd, hd⟩ := hD K (r ≫ pullback.snd p q)
    obtain ⟨c₀, hc₀, hce, hcd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_colimitCone_pullback_with_snd p q hp r ce cd
      he (hpc K _ ce he) hd (hqc K _ cd hd)
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso c₀ c hc₀ hc
    have hcd' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (pullback.snd p q) c₀) :=
      hcd.symm ▸ hd
    exact ⟨hce.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp r (pullback.fst p q))),
      hcd'.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp r (pullback.snd p q)))⟩
  · rintro ⟨he, hd⟩
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_of_isPullback_of_components (IsPullback.of_hasPullback p q)
      c he hd (hpc K _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (pullback.fst p q) c) he)

/-- 概要：余極限保存関手の引き戻しの第一射影は全小余極限を保存する。
方針：元の全余錐の成分判定を使う。
規約：元の射影自身の保存性を結論する。
使われ方：Pr^L の引き戻し錐。 -/
lemma pullback_fst_preservesSmallColimits : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (pullback.fst p q) := by
  intro K r c hc
  exact ((pullback_isColimitCone_iff_components p q hp hE hD hpc hqc c).mp hc).1

/-- 概要：余極限保存関手の引き戻しの第二射影は全小余極限を保存する。
方針：元の全余錐の成分判定を使う。
規約：元の射影自身の保存性を結論する。
使われ方：Pr^L の引き戻し錐。 -/
lemma pullback_snd_preservesSmallColimits : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (pullback.snd p q) := by
  intro K r c hc
  exact ((pullback_isColimitCone_iff_components p q hp hE hD hpc hqc c).mp hc).2

/-- 概要：引き戻しへの関手の全小余極限保存は両成分の保存と同値。
方針：同じ元の余錐の像を両射影で判定する。
規約：始域の余完備性は要求しない。
使われ方：Pr^L 内の引き戻しの普遍性。 -/
lemma pullback_preservesSmallColimits_iff_components {C : SSet.{u + 1}}
    (F : C ⟶ pullback p q) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits F ↔ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (F ≫ pullback.fst p q) ∧
      _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits (F ≫ pullback.snd p q) := by
  constructor
  · intro hF
    constructor
    · intro K r c hc
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using
        ((pullback_isColimitCone_iff_components p q hp hE hD hpc hqc
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)).mp (hF K r c hc)).1
    · intro K r c hc
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using
        ((pullback_isColimitCone_iff_components p q hp hE hD hpc hqc
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)).mp (hF K r c hc)).2
  · rintro ⟨he, hd⟩ K r c hc
    apply (pullback_isColimitCone_iff_components p q hp hE hD hpc hqc
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)).mpr
    constructor
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using he K r c hc
    · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc] using hd K r c hc

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.4.5.5" (partial := stronger-hyp) "仮定：一方が categorical fibration である strict pullback、両側が小余完備で両脚が全小余極限保存（Lean が強い：原典の特定 K の存在・保存より強い）。結論：同じ引き戻しに全 K-余極限が存在し、その元の全余錐の余極限性は両射影での余極限性と同値（結論は一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_hasSmallColimits
attribute [cite HTT "5.4.5.5" (partial := stronger-hyp) "仮定：一方が categorical fibration である strict pullback、両側が小余完備で両脚が全小余極限保存（Lean が強い：原典の特定 K の存在・保存より強い）。結論：同じ引き戻しに全 K-余極限が存在し、その元の全余錐の余極限性は両射影での余極限性と同値（結論は一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_isColimitCone_iff_components
attribute [cite HTT "5.5.3.12" (partial := special) "仮定：presentable な三準圏と全小余極限保存な両脚（Lean が強い：元の平方は一方が categorical lifting を持つ strict pullback）。結論：同じ引き戻しが presentable、元の引き戻しへの関手の全小余極限保存の成分判定（この模型で一致）。汎用 accessibility 命題の入力は実証済みの AccessiblePullback.pullback_isAccessible で供給できる。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_preservesSmallColimits_iff_components

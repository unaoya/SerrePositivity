module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

/-!
概要：presentable 性と全小余極限の存在・保存を、元の全同値によって輸送する。
方針：逆関手に戻した全図式の余錐を同じ順関手で写し、元の全自然同型で回収する。
規約：任意の小さい単体集合形状と元の全余錐を保持する。Ind の余極限存在は仮定から区別する。
使われ方：HTT 5.5.1 の前層・Ind 表現の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 元の全同値は、指定された全ての小余極限余錐を保存する。 -/
lemma equivalence_preservesSmallColimits {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] {F : C ⟶ E} (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence F) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits F := by
  intro K D c hc
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff hF c).mp hc

/-- 全ての小余極限の存在は、元の同じ全同値で輸送される。 -/
lemma HasSmallColimits.of_equivalence {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E := by
  intro K D
  obtain ⟨c, hc⟩ := hC K (D ≫ e.inv)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((D ≫ e.inv) ≫ e.hom) D := by
    simpa only [Category.assoc, Category.comp_id] using e.invHomIso.precomp D
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_functorIso he).mp
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone e.hom c, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.equivalence_isColimitCone_iff e.isQCatEquivalence c).mp hc⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.HasSmallColimits (of_equivalence)


/-- 元の全同値は presentable 性を保存する。 -/
lemma IsPresentable.of_equivalence {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E) : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isAccessible_iff_equivalence e).mp hC.1, hC.2.of_equivalence e⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable (of_equivalence)


/-- 元の全同値による presentable 性の保存・反映。 -/
lemma isPresentable_iff_equivalence {C E : SSet.{u + 1}}
    [Quasicategory C] [Quasicategory E] (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence C E) :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C ↔ _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E :=
  ⟨fun h ↦ h.of_equivalence e, fun h ↦ h.of_equivalence e.symm⟩

/-- presentable 圏は、小余極限を持つ同じ小さい Ind 模型との全同値を持つ。 -/
lemma isPresentable_iff_cocompleteIndEquivalence (C : SSet.{u + 1}) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C ↔ ∃ (κ : Cardinal.{u}), κ.IsRegular ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) ∧
          Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) C) := by
  constructor
  · intro hC
    obtain ⟨κ, hκ⟩ := hC.1
    obtain ⟨A, hA, ⟨e⟩⟩ := hκ.exists_indEquivalence
    have := hA
    exact ⟨κ, hκ.1, A, hA, hC.2.of_equivalence e.symm, ⟨e⟩⟩
  · rintro ⟨κ, hκ, A, hA, hc, ⟨e⟩⟩
    have := hA
    have : Fact κ.IsRegular := ⟨hκ⟩
    exact (IsPresentable.of_equivalence
      ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInfinity_isKappaAccessible κ A).isAccessible, hc⟩ e)

/-- presentable 圏の accessibility は、同じ宇宙の任意の上限を超える濃度で実現できる。 -/
lemma IsPresentable.exists_accessibilityCardinalAbove {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, σ < μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C := hC.1.exists_larger σ

with_weak_namespace _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsPresentable (exists_accessibilityCardinalAbove)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.4.4.2" (partial := component) "仮定：準圏（Lean が弱い：安定性は不要）。結論：presentable なら局所小で、余完備な Ind 模型による presentable 性の判定（Lean が弱い：小余積・hC の局所小性・単一の κ コンパクト生成対象という三条件の判定を与えない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_cocompleteIndEquivalence
attribute [cite HTT "5.5.3.10" (partial := special) "仮定：presentable C と終対象 x の一点図式（Lean が強い：一般の小図式 p を終対象の一点に限定）。結論：同じ C/x の元の射影が全準圏同値であるため C/x は presentable（この場合に一致）。元の射影の同値は終対象の境界条件から構成でき、別の圏との未供給比較ではない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_equivalence
attribute [cite HTT "5.5.3.11" (partial := special) "仮定：presentable C と始対象 x の一点図式（Lean が強い：p を始対象の一点に限定）。結論：同じ Cx/ の元の射影が全準圏同値なので Cx/ は presentable（この場合に一致）。一般の小図式の下圏の compact 生成性は結論しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_equivalence
attribute [cite HTT "5.5.3.14" (partial := special) "仮定：presentable fibration p:X→S（Lean が強い：小基底 S は始対象 s を持つ準圏）。結論：同じ全 coCartesian 切断準圏の s での評価が実ファイバー Xs との全準圏同値であるため、同じ切断準圏が presentable（この場合に一致）。一般の小 S の極限や、coCartesian 条件を課さない全切断へは拡張しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isPresentable_iff_equivalence

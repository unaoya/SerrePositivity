module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.SpanPresentations.FiniteDiagramSpanLifts
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ContinuousKanFiniteFactorization
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.ContinuousKanHomotopy

/-! # Kan 置換後の任意の有限図式のホモトピー持ち上げ

概要：有限対充填を持つ射の連続 Kan 置換は、任意の有限図式をホモトピー類で持ち上げる。
方針：商側の有限部分複体へ因子化し、その包含の元の持ち上げと比較を Kan 置換で送る。
規約：単位の自然性と証明済みの連続性を使う。使われ方：実屋根比較の弱同値判定の全射側。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet

/-- Kan 置換後の任意の有限図式は、同じ有限形状の元図式の像へホモトピックである。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteDiagramLift {E Q : SSet.{u}} {F : E ⟶ Q}
    (hF : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers F) {K : SSet.{u}} [K.Finite]
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj Q) :
    ∃ f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj E,
      Nonempty (SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F) g) := by
  obtain ⟨B, v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_finite_factorization g
  obtain ⟨t, ⟨H⟩⟩ := hF.finiteDiagramLift B.val.ι
  obtain ⟨R⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_map_homotopy H
  let f := v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map t
  refine ⟨f, ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp R v) ?_ hv⟩⟩
  change v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (t ≫ F) =
    (v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map t) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Kan 置換後の比較は、全ての有限パラメータの写像空間の連結成分上で全射。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteDiagramPiZero_surjective
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers F)
    (K : SSet.{u}) [K.Finite] : Function.Surjective
      (SSet.mapπ₀ ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F))) := by
  intro z
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective z
  obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj Q)).surjective v
  obtain ⟨f, ⟨H⟩⟩ := hF.kanFiniteDiagramLift g
  refine ⟨SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f), ?_⟩
  change SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map F)) =
    SSet.π₀.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨H⟩

/-- 任意の有限射の比較図式は、Kan 置換後で指定始域に同じホモトピー類を持つ切断を持つ。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteRelativeSection
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.HasFiniteHomotopyRelativeFillers F)
    {A B : SSet.{u}} [A.Finite] [B.Finite] (j : A ⟶ B) (a : A ⟶ E) (b : B ⟶ Q)
    (ha : a ≫ F = j ≫ b) :
    ∃ t : B ⟶ E, Nonempty (SSet.Homotopy (t ≫ F) b) ∧
      Nonempty (SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (j ≫ t))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map a)) := by
  obtain ⟨t, ht, u, ⟨H₀⟩, ⟨H₁⟩⟩ := hF.finiteDiagramSpanLift j a b ha
  obtain ⟨R₀⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_map_homotopy H₀
  obtain ⟨R₁⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.continuousKanReplacement_map_homotopy H₁
  have h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨R₀⟩
  have h₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨R₁⟩
  exact ⟨t, ht, (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_piZero_eq_iff_homotopy _ _).1 (h₁.symm.trans h₀)⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories

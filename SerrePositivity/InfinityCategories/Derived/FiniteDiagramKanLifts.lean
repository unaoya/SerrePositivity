module
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Derived.FiniteDiagramSpanLifts
public import SerrePositivity.InfinityCategories.F2.ContinuousKanFiniteFactorization
public import SerrePositivity.InfinityCategories.F2.ContinuousKanHomotopy

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet F2

/-- Kan 置換後の任意の有限図式は、同じ有限形状の元図式の像へホモトピックである。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteDiagramLift {E Q : SSet.{u}} {F : E ⟶ Q}
    (hF : HasFiniteHomotopyRelativeFillers F) {K : SSet.{u}} [K.Finite]
    (g : K ⟶ continuousKanReplacement.obj Q) :
    ∃ f : K ⟶ continuousKanReplacement.obj E,
      Nonempty (SSet.Homotopy (f ≫ continuousKanReplacement.map F) g) := by
  obtain ⟨B, v, hv⟩ := continuousKanReplacement_finite_factorization g
  obtain ⟨t, ⟨H⟩⟩ := hF.finiteDiagramLift B.val.ι
  obtain ⟨R⟩ := continuousKanReplacement_map_homotopy H
  let f := v ≫ continuousKanReplacement.map t
  refine ⟨f, ⟨stableHomotopyRetarget (functorHomotopyPrecomp R v) ?_ hv⟩⟩
  change v ≫ continuousKanReplacement.map (t ≫ F) =
    (v ≫ continuousKanReplacement.map t) ≫ continuousKanReplacement.map F
  rw [CategoryTheory.Functor.map_comp, Category.assoc]

/-- Kan 置換後の比較は、全ての有限パラメータの写像空間の連結成分上で全射。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteDiagramPiZero_surjective
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : HasFiniteHomotopyRelativeFillers F)
    (K : SSet.{u}) [K.Finite] : Function.Surjective
      (SSet.mapπ₀ ((ihom K).map (continuousKanReplacement.map F))) := by
  intro z
  obtain ⟨v, rfl⟩ := SSet.π₀.mk_surjective z
  obtain ⟨g, rfl⟩ := (functorVertexEquiv K (continuousKanReplacement.obj Q)).surjective v
  obtain ⟨f, ⟨H⟩⟩ := hF.kanFiniteDiagramLift g
  refine ⟨SSet.π₀.mk (functorVertex f), ?_⟩
  change SSet.π₀.mk (functorVertex (f ≫ continuousKanReplacement.map F)) =
    SSet.π₀.mk (functorVertex g)
  exact (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨H⟩

/-- 任意の有限射の比較図式は、Kan 置換後で指定始域に同じホモトピー類を持つ切断を持つ。 -/
lemma HasFiniteHomotopyRelativeFillers.kanFiniteRelativeSection
    {E Q : SSet.{u}} {F : E ⟶ Q} (hF : HasFiniteHomotopyRelativeFillers F)
    {A B : SSet.{u}} [A.Finite] [B.Finite] (j : A ⟶ B) (a : A ⟶ E) (b : B ⟶ Q)
    (ha : a ≫ F = j ≫ b) :
    ∃ t : B ⟶ E, Nonempty (SSet.Homotopy (t ≫ F) b) ∧
      Nonempty (SSet.Homotopy (continuousKanReplacement.map (j ≫ t))
        (continuousKanReplacement.map a)) := by
  obtain ⟨t, ht, u, ⟨H₀⟩, ⟨H₁⟩⟩ := hF.finiteDiagramSpanLift j a b ha
  obtain ⟨R₀⟩ := continuousKanReplacement_map_homotopy H₀
  obtain ⟨R₁⟩ := continuousKanReplacement_map_homotopy H₁
  have h₀ := (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨R₀⟩
  have h₁ := (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨R₁⟩
  exact ⟨t, ht, (functorVertex_piZero_eq_iff_homotopy _ _).1 (h₁.symm.trans h₀)⟩

end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.Derived.RoofLeftPrismLift
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.SlicePrismSquare

/-! # 左ファイブレーションの終対象 fiber への全体評価

概要：終対象への全錐を使い、全空間から終対象 fiber への一つの実評価と実比較を構成する。
方針：終対象 slice の切断と left anodyne prism の持ち上げを接続する。
規約：モデル構造・有限性を仮定しない。使われ方：任意標的への屋根評価の全体構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
/-- 終対象への slice 切断を、その同じ join 写像から実 prism に展開する。 -/
def roofTerminalSectionPrism {B : SSet.{u}} (t : B _⦋0⦌)
    (σ : B ⟶ sliceOver (SSet.yonedaEquiv.symm t)) : (Δ[1] : SSet.{u}) ⊗ B ⟶ B :=
  rightMappingSpacePrism B ≫ sliceOverUncurry σ
/-- 切断の終対象 prism の零端は、切断の元の始域射影。 -/
lemma roofTerminalSectionPrism_zero {B : SSet.{u}} (t : B _⦋0⦌)
    (σ : B ⟶ sliceOver (SSet.yonedaEquiv.symm t)) :
    prismEndpoint 0 B ≫ roofTerminalSectionPrism t σ = σ ≫ sliceOverProjection _ := by
  rw [roofTerminalSectionPrism, ← Category.assoc, rightMappingSpacePrism_zero,
    sliceOverUncurry_projection]
/-- 切断の終対象 prism の一端は、指定終対象に厳密に定値。 -/
lemma roofTerminalSectionPrism_one {B : SSet.{u}} (t : B _⦋0⦌)
    (σ : B ⟶ sliceOver (SSet.yonedaEquiv.symm t)) :
    prismEndpoint 1 B ≫ roofTerminalSectionPrism t σ = SSet.const t := by
  rw [roofTerminalSectionPrism, ← Category.assoc, rightMappingSpacePrism_one,
    Category.assoc, sliceOverUncurry_fixed, const_point_comp_yoneda]
/-- 終対象への全錐、全空間の fiber への実評価、同じ全底を持つ実ホモトピー。 -/
structure RoofTerminalEvaluation {E B : SSet.{u}} (p : E ⟶ B) (t : B _⦋0⦌) where
  coneSection : B ⟶ sliceOver (SSet.yonedaEquiv.symm t)
  coneSection_projection : coneSection ≫ sliceOverProjection _ = 𝟙 B
  evaluation : E ⟶ vertexFiber p t
  homotopy : SSet.Homotopy (𝟙 E) (evaluation ≫ vertexFiberι p t)
  homotopy_over : homotopy.h ≫ p =
    (β_ E (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ p) ≫ roofTerminalSectionPrism t coneSection

/-- fiber の同型で評価と包含を共役しても、全空間への同じ評価写像を回収する。 -/
lemma roofEvaluationIso_transport {E V Z : SSet.{u}} (e : V ≅ Z) (c : E ⟶ V) (j : V ⟶ E) :
    c ≫ j = (c ≫ e.hom) ≫ (e.inv ≫ j) := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
/-- 左ファイブレーションと終対象は、全空間の実評価と全底付き実比較を供給する。 -/
lemma roofLeftFibration_terminalEvaluation_nonempty {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (t : B _⦋0⦌) (ht : IsTerminalVertex t) :
    Nonempty (RoofTerminalEvaluation p t) := by
  have : TrivialKanFibration (sliceOverProjection (SSet.yonedaEquiv.symm t)) :=
    (isTerminalVertex_iff_trivialKanFibration t).mp ht
  obtain ⟨σ, hσ⟩ := trivialKanFibration_exists_section
    (sliceOverProjection (SSet.yonedaEquiv.symm t))
  let β := (Δ[1] ◁ p) ≫ roofTerminalSectionPrism t σ
  have hβ₀ : (𝟙 E) ≫ p = prismEndpoint 0 E ≫ β := by
    dsimp only [β]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      roofTerminalSectionPrism_zero, hσ, Category.comp_id, Category.id_comp]
  obtain ⟨H, hH₀, hHp⟩ := roofLeftFibration_lift_start_prism p (𝟙 E) β hβ₀
  let a := prismEndpoint 1 E ≫ H
  have ha : a ≫ p = SSet.const t := by
    change (prismEndpoint 1 E ≫ H) ≫ p = _
    rw [Category.assoc, hHp]
    dsimp only [β]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      roofTerminalSectionPrism_one, SSet.comp_const]
  let c := vertexFiberLift p t a ha
  let h : SSet.Homotopy (𝟙 E) (c ≫ vertexFiberι p t) := {
    h := (β_ E (Δ[1] : SSet.{u})).hom ≫ H
    h₀ := by
      change prismEndpoint 0 E ≫ H = 𝟙 E
      exact hH₀
    h₁ := by
      change prismEndpoint 1 E ≫ H = c ≫ vertexFiberι p t
      exact (vertexFiberLift_ι p t a ha).symm
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  refine ⟨⟨σ, hσ, c, h, ?_⟩⟩
  change ((β_ E (Δ[1] : SSet.{u})).hom ≫ H) ≫ p = _
  rw [Category.assoc, hHp]
end SerrePositivity.InfinityCategories

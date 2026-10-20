module
public import SerrePositivity.InfinityCategories.F1B.CofinalFixedPrism
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
/-!
概要：指定部分の評価と全時刻の比較を保ち、同じ底のホモトピー上で全体を fiber に評価する。
方針：始端固定の相対 left fibration prism を使い、終端を指定 fiber へ戻す。
規約：指定部分は任意の単射。使われ方：屋根評価の全相対高次境界への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
/-- 指定部分の評価と比較を全時刻で保つ、同じ底の fiber への相対評価。 -/
structure RoofRelativeEvaluation {L K E B : SSet.{u}} (p : E ⟶ B) (t : B _⦋0⦌)
    (i : L ⟶ K) (a : K ⟶ E) (e : L ⟶ vertexFiber p t)
    (H : SSet.Homotopy (i ≫ a) (e ≫ vertexFiberι p t))
    (β : SSet.Homotopy (a ≫ p) (SSet.const t)) where
  evaluation : K ⟶ vertexFiber p t
  evaluation_boundary : i ≫ evaluation = e
  homotopy : SSet.Homotopy a (evaluation ≫ vertexFiberι p t)
  over : homotopy.h ≫ p = β.h
  boundary : (i ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h = H.h
/-- 任意の指定部分の実評価と全比較を保って、同じ全底上の実評価を延長できる。 -/
lemma roofRelativeEvaluation_nonempty {L K E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (t : B _⦋0⦌) (i : L ⟶ K) [Mono i]
    (a : K ⟶ E) (e : L ⟶ vertexFiber p t)
    (H : SSet.Homotopy (i ≫ a) (e ≫ vertexFiberι p t))
    (β : SSet.Homotopy (a ≫ p) (SSet.const t))
    (hH : H.h ≫ p = (i ▷ (Δ[1] : SSet.{u})) ≫ β.h) :
    Nonempty (RoofRelativeEvaluation p t i a e H β) := by
  let G := (β_ (Δ[1] : SSet.{u}) L).hom ≫ H.h
  let γ := (β_ (Δ[1] : SSet.{u}) K).hom ≫ β.h
  have h₀ : prismEndpoint 0 L ≫ G = i ≫ a := H.h₀
  have hG : G ≫ p = (Δ[1] ◁ i) ≫ γ := by
    dsimp only [G, γ]
    rw [Category.assoc, hH, ← Category.assoc]
    rfl
  have hβ : a ≫ p = prismEndpoint 0 K ≫ γ := β.h₀.symm
  obtain ⟨J, hJboundary, hJstart, hJover⟩ := leftFibration_lift_fixed_prism
    i p G a γ h₀ hG hβ
  let v := prismEndpoint 1 K ≫ J
  have hv : v ≫ p = SSet.const t := by
    dsimp only [v]
    rw [Category.assoc, hJover]
    exact β.h₁
  let f := vertexFiberLift p t v hv
  have hf : f ≫ vertexFiberι p t = v := vertexFiberLift_ι p t v hv
  let T : SSet.Homotopy a (f ≫ vertexFiberι p t) := {
    h := (β_ K (Δ[1] : SSet.{u})).hom ≫ J
    h₀ := hJstart
    h₁ := hf.symm
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  have hT : (i ▷ (Δ[1] : SSet.{u})) ≫ T.h = H.h := by
    change (i ▷ (Δ[1] : SSet.{u})) ≫ ((β_ K (Δ[1] : SSet.{u})).hom ≫ J) = _
    have he : (i ▷ (Δ[1] : SSet.{u})) ≫ (β_ K (Δ[1] : SSet.{u})).hom =
        (β_ L (Δ[1] : SSet.{u})).hom ≫ (Δ[1] ◁ i) := rfl
    rw [← Category.assoc, he, Category.assoc, hJboundary]
    dsimp only [G]
    simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have he : i ≫ f = e := by
    apply (cancel_mono (vertexFiberι p t)).mp
    have h := congrArg (fun g => SSet.ι₁ ≫ g) hT
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, T.h₁, H.h₁] at h
    simpa only [Category.assoc] using h
  refine ⟨⟨f, he, T, ?_, hT⟩⟩
  change ((β_ K (Δ[1] : SSet.{u})).hom ≫ J) ≫ p = _
  rw [Category.assoc, hJover]
  dsimp only [γ]
  simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
end SerrePositivity.InfinityCategories

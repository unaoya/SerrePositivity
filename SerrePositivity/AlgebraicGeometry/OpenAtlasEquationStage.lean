module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasEquationFamily

/-!
概要：六種の gluing の式を同時に満たす、実際の後の係数段を供給する。
方針：具体的な有限族を既存の係数段への同時一致判定へ渡す。
規約：元の環への射に忠実平坦性は仮定せず、式の存在を追加仮定にしない。
使われ方：G2 の実際の有限段の gluing datum の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {k : Type v} [CommRing k] [IsNoetherianRing k]
  {R : Type u} [CommRing R] [Algebra k R]
  {I : Type u} {X : Scheme.{u}} {U : I → Scheme.{u}} {j : ∀ i, U i ⟶ X}
  [∀ i, IsOpenImmersion (j i)] {f : X ⟶ Spec (CommRingCat.of R)}
  (m : OpenAtlasModelData k U j f)
  {B : Scheme.{u}} (b : Spec (CommRingCat.of R) ⟶ B)
  (γ : B ⟶ Spec (CommRingCat.of m.A))
  (h : b ≫ γ = Spec.map (CommRingCat.ofHom (algebraMap m.A R)))

variable (l : ∀ e, pullback γ (m.atlasArrowFamily e).sourceMap ⟶
    pullback γ (m.atlasArrowFamily e).targetMap)
  (hl : ∀ e, l e ≫ pullback.fst γ (m.atlasArrowFamily e).targetMap =
    pullback.fst γ (m.atlasArrowFamily e).sourceMap)
  (hn : ∀ e, (m.atlasArrowFamily e).comparisonAt b γ h ≫ l e ≫
    pullback.snd γ (m.atlasArrowFamily e).targetMap = (m.atlasArrowFamily e).arrow)
/-- 六種の具体的な式が、指定した後の段の実際の底変換射として全て成立する。 -/
def stageEquationsHold {C : Scheme.{u}} (δ : C ⟶ B) : Prop :=
  ∀ e, let a := m.atlasEquationFamily b γ h l hl hn e
    baseChangedModelArrow δ a.sourceMap a.targetMap a.left a.leftOver =
      baseChangedModelArrow δ a.sourceMap a.targetMap a.right a.rightOver

/-- 六種の式を同時に満たす、実際の有限生成係数部分代数の後の段を供給する。 -/
theorem exists_stageEquationsHold_of_fg [Finite I]
    (A : Subalgebra k R) (hA : A.FG)
    (γ₁ : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of m.A))
    (h₁ : Spec.map (CommRingCat.ofHom (algebraMap A R)) ≫ γ₁ =
      Spec.map (CommRingCat.ofHom (algebraMap m.A R)))
    (l₁ : ∀ e, pullback γ₁ (m.atlasArrowFamily e).sourceMap ⟶
      pullback γ₁ (m.atlasArrowFamily e).targetMap)
    (hl₁ : ∀ e, l₁ e ≫ pullback.fst γ₁ (m.atlasArrowFamily e).targetMap =
      pullback.fst γ₁ (m.atlasArrowFamily e).sourceMap)
    (hn₁ : ∀ e, (m.atlasArrowFamily e).comparisonAt
      (Spec.map (CommRingCat.ofHom (algebraMap A R))) γ₁ h₁ ≫ l₁ e ≫
        pullback.snd γ₁ (m.atlasArrowFamily e).targetMap = (m.atlasArrowFamily e).arrow) :
    ∃ (s : Finset R)
      (δ : (coefficientSpecDiagram k R).obj (.op s) ⟶ Spec (CommRingCat.of A)),
      (coefficientSpecCone k R).π.app (.op s) ≫ δ =
          Spec.map (CommRingCat.ofHom (algebraMap A R)) ∧
        m.stageEquationsHold (Spec.map (CommRingCat.ofHom (algebraMap A R))) γ₁ h₁ l₁ hl₁ hn₁ δ := by
  exact CartesianModelEquation.exists_coefficient_stage k R A hA
    (m.atlasEquationFamily (Spec.map (CommRingCat.ofHom (algebraMap A R))) γ₁ h₁ l₁ hl₁ hn₁)

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData

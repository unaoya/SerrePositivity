module

public import SerrePositivity.AlgebraicGeometry.CartesianModelArrow
public import SerrePositivity.AlgebraicGeometry.CoefficientSubalgebraFactor

/-!
概要：有限個の具体的な模型の射を、実際の有限生成係数部分代数の同じ段へ降ろす。
方針：元の源からの比較を pullback lift で保持し、既存の同時降下の射影と照合する。
規約：係数段の元の環への忠実平坦性は要求しない。
使われ方：G2 のアトラスの対角・反転・三重交叉の射の供給。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v w

/-- 元の源から段の底変換模型への実際の比較。 -/
def CartesianModelArrow.comparisonAt {T S B : Scheme.{u}} {g : T ⟶ S}
    (a : CartesianModelArrow g) (b : T ⟶ B) (γ : B ⟶ S) (h : b ≫ γ = g) :
    a.source ⟶ pullback γ a.sourceMap :=
  pullback.lift (a.base ≫ b) a.comparison (by rw [Category.assoc, h, a.cartesian.w])

/-- 実際の比較は、元の源を頂点に保つ Cartesian cone の同じ射影。 -/
theorem CartesianModelArrow.comparisonAt_eq_coneProjection
    {J : Type u} [SmallCategory J] (D : J ⥤ Scheme.{u}) (c : Cone D) (i : J)
    {S : Scheme.{u}} (γ : D.obj i ⟶ S) (g : c.pt ⟶ S) (hγ : c.π.app i ≫ γ = g)
    (a : CartesianModelArrow g) (j : Over i)
    (h : c.π.app j.left ≫ (D.map j.hom ≫ γ) = g) :
    a.comparisonAt (c.π.app j.left) (D.map j.hom ≫ γ) h =
      (cartesianCompositeStageCone D c i γ a.sourceMap g hγ
        a.comparison a.base a.cartesian).π.app j := by
  apply pullback.hom_ext
  · simp only [CartesianModelArrow.comparisonAt, pullback.lift_fst,
      cartesianCompositeStageCone_π_fst]
  · simp only [CartesianModelArrow.comparisonAt, pullback.lift_snd,
      cartesianCompositeStageCone_π_snd]

/-- 有限族の元の射を、具体的な有限生成係数部分代数の一つの段へ同時に降ろす。 -/
theorem CartesianModelArrow.exists_coefficient_stage
    (k : Type v) (R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (A : Subalgebra k R) (hA : A.FG)
    {ι : Type w} [Finite ι]
    (a : ι → CartesianModelArrow (Spec.map (CommRingCat.ofHom (algebraMap A R)))) :
    ∃ (s : Finset R)
      (γ : (coefficientSpecDiagram k R).obj (.op s) ⟶ Spec (CommRingCat.of A))
      (hγ : (coefficientSpecCone k R).π.app (.op s) ≫ γ =
        Spec.map (CommRingCat.ofHom (algebraMap A R)))
      (l : ∀ e, pullback γ (a e).sourceMap ⟶ pullback γ (a e).targetMap),
      ∀ e, l e ≫ pullback.fst γ (a e).targetMap = pullback.fst γ (a e).sourceMap ∧
        (a e).comparisonAt ((coefficientSpecCone k R).π.app (.op s)) γ hγ ≫
          l e ≫ pullback.snd γ (a e).targetMap = (a e).arrow := by
  let D := coefficientSpecDiagram k R
  let c := coefficientSpecCone k R
  have hc : IsLimit c := coefficientSpecConeIsLimit k R
  obtain ⟨s, γ, hγ⟩ := exists_coefficient_spec_factor_of_fg k R A hA
  haveI (b : (Finset R)ᵒᵖ) : CompactSpace (D.obj b) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI (b : (Finset R)ᵒᵖ) : QuasiSeparatedSpace (D.obj b) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  haveI {b d : (Finset R)ᵒᵖ} (q : b ⟶ d) : IsAffineHom (D.map q) := by
    dsimp [D, coefficientSpecDiagram]; infer_instance
  obtain ⟨j, l, hl⟩ := CartesianModelArrow.exists_common_stage D c hc (.op s) γ _ hγ a
  have h : c.π.app j.left ≫ (D.map j.hom ≫ γ) =
      Spec.map (CommRingCat.ofHom (algebraMap A R)) := by
    rw [← Category.assoc, c.w, hγ]
  refine ⟨j.left.unop, D.map j.hom ≫ γ, h, l, ?_⟩
  intro e
  refine ⟨(hl e).1, ?_⟩
  rw [CartesianModelArrow.comparisonAt_eq_coneProjection D c (.op s) γ _ hγ (a e) j h]
  exact (hl e).2

end SerrePositivity.AlgebraicGeometry

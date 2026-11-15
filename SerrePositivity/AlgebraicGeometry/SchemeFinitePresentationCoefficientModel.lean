module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasGluedModel

/-!
概要：任意の affine 基底上の qcqs な局所有限表示対象を、実際の有限生成係数部分代数へ降ろす。
方針：有限 affine アトラス模型、三種の射と六種の式の共通段、実際の gluing を組み合わせる。
規約：Stacks 01ZM の対象の降下。元の環 R の Noether 性・模型の存在は仮定しない。
使われ方：G2 の固有模型の供給の、一般の有限表示対象の模型の部分。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v

/-- qcqs な局所有限表示対象の、実際の有限生成係数部分代数上の模型と Cartesian 比較。 -/
theorem exists_finitePresentation_coefficient_model
    (k : Type v) (R : Type u) [CommRing k] [IsNoetherianRing k] [CommRing R] [Algebra k R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    ∃ (A : Subalgebra k R), A.FG ∧ ∃ (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of A)),
      LocallyOfFinitePresentation p ∧ QuasiCompact p ∧ QuasiSeparated p ∧
        ∃ a : X ⟶ Y, IsPullback a f p (Spec.map (CommRingCat.ofHom (algebraMap A R))) := by
  obtain ⟨𝒰, hFin, hAff, ⟨m⟩⟩ := exists_finite_openAtlasModel k R f
  letI : Finite 𝒰.I₀ := hFin
  obtain ⟨s₁, γ₁, h₁, l, hall⟩ := CartesianModelArrow.exists_coefficient_stage k R m.A m.fg
    m.atlasArrowFamily
  let A₁ := Algebra.adjoin k (s₁ : Set R)
  have hι₁ : CommRingCat.ofHom (Algebra.adjoin k (s₁ : Set R)).val.toRingHom =
      CommRingCat.ofHom (algebraMap A₁ R) := by ext x; rfl
  have h₁' : Spec.map (CommRingCat.ofHom (algebraMap A₁ R)) ≫ γ₁ =
      Spec.map (CommRingCat.ofHom (algebraMap m.A R)) := by
    simpa only [coefficientSpecCone_projection, hι₁] using h₁
  have hl (e) := (hall e).1
  have hn (e) : (m.atlasArrowFamily e).comparisonAt
      (Spec.map (CommRingCat.ofHom (algebraMap A₁ R))) γ₁ h₁' ≫ l e ≫
        pullback.snd γ₁ (m.atlasArrowFamily e).targetMap = (m.atlasArrowFamily e).arrow := by
    simpa only [coefficientSpecCone_projection, hι₁] using (hall e).2
  obtain ⟨s₂, δ, hδ, hEq⟩ := m.exists_stageEquationsHold_of_fg A₁
    (Subalgebra.fg_adjoin_finset s₁) γ₁ h₁' l hl hn
  let A₂ := Algebra.adjoin k (s₂ : Set R)
  have hι₂ : CommRingCat.ofHom (Algebra.adjoin k (s₂ : Set R)).val.toRingHom =
      CommRingCat.ofHom (algebraMap A₂ R) := by ext x; rfl
  letI : IsNoetherianRing A₂ := isNoetherianRing_of_fg (Subalgebra.fg_adjoin_finset s₂)
  haveI : IsAffine ((coefficientSpecDiagram k R).obj (.op s₂)) := by
    change IsAffine (Spec (CommRingCat.of A₂)); infer_instance
  haveI : IsLocallyNoetherian ((coefficientSpecDiagram k R).obj (.op s₂)) := by
    change IsLocallyNoetherian (Spec (CommRingCat.of A₂)); infer_instance
  obtain ⟨Y, p, hfp, hq, hs, a, hpb⟩ := m.exists_glued_model
    (Spec.map (CommRingCat.ofHom (algebraMap A₁ R))) γ₁ h₁' l hl hn 𝒰.exists_eq
    ((coefficientSpecCone k R).π.app (.op s₂)) δ hδ hEq
  refine ⟨A₂, Subalgebra.fg_adjoin_finset s₂, Y, p, hfp, hq, hs, a, ?_⟩
  simpa only [coefficientSpecCone_projection, hι₂] using hpb

end SerrePositivity.AlgebraicGeometry

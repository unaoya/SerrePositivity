module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
概要：affine 基底上の有限表示なスキームから、元の構造射を保つ有限アフィンアトラスを取る。
方針：有限アフィン開被覆の各項を Spec に直し、有限表示性を同じ構造射で読む。
規約：Noether 性・v 判定を要求しない。
使われ方：G2 の共通係数部分代数上の有限アトラスの模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 有限表示な affine 基底への射は、同じ構造射を保つ有限表示代数の有限アトラスを持つ。 -/
theorem exists_finite_affine_presentation_atlas {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) [LocallyOfFinitePresentation f] [QuasiCompact f] :
    ∃ (n : ℕ) (B : Fin n → CommRingCat.{u}) (b : ∀ i, R ⟶ B i)
      (k : ∀ i, Spec (B i) ⟶ X),
      (∀ i, IsOpenImmersion (k i) ∧ (b i).hom.FinitePresentation ∧
        k i ≫ f = Spec.map (b i)) ∧ ∀ x : X, ∃ i z, k i z = x := by
  classical
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec _))
  let e := Fintype.equivFin 𝒰.I₀
  let B (i : Fin (Fintype.card 𝒰.I₀)) : CommRingCat.{u} := Γ(𝒰.X (e.symm i), ⊤)
  let k (i : Fin (Fintype.card 𝒰.I₀)) : Spec (B i) ⟶ X :=
    (𝒰.X (e.symm i)).isoSpec.inv ≫ 𝒰.f (e.symm i)
  let b (i : Fin (Fintype.card 𝒰.I₀)) : R ⟶ B i := Spec.preimage (k i ≫ f)
  have hfac (i : Fin (Fintype.card 𝒰.I₀)) : k i ≫ f = Spec.map (b i) :=
    (Spec.map_preimage (k i ≫ f)).symm
  refine ⟨_, B, b, k, ?_, ?_⟩
  · intro i
    haveI : IsOpenImmersion (k i) := by dsimp [k]; infer_instance
    haveI : LocallyOfFinitePresentation (k i ≫ f) := inferInstance
    refine ⟨inferInstance, ?_, hfac i⟩
    exact (LocallyOfFinitePresentation.SpecMap_iff (b i)).mp
      ((hfac i) ▸ (inferInstance : LocallyOfFinitePresentation (k i ≫ f)))
  · intro x
    obtain ⟨a, z, hz⟩ := 𝒰.exists_eq x
    refine ⟨e a, ?_⟩
    change ∃ w : Spec Γ(𝒰.X (e.symm (e a)), ⊤),
      ((𝒰.X (e.symm (e a))).isoSpec.inv ≫ 𝒰.f (e.symm (e a))) w = x
    have he : e.symm (e a) = a := e.symm_apply_apply a
    rw [he]
    refine ⟨(𝒰.X a).isoSpec.hom z, ?_⟩
    rw [Scheme.Hom.comp_apply]
    have h : (𝒰.X a).isoSpec.inv ((𝒰.X a).isoSpec.hom z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
      rfl
    rw [h]
    exact hz

end SerrePositivity.AlgebraicGeometry

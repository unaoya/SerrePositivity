module

public import SerrePositivity.AlgebraicGeometry.SchemeVCoverOpenCover
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-!
概要：affine 基底への準コンパクトな局所有限表示 v 被覆を、有限表示な affine 被覆で細分する。
方針：有限アフィン開被覆の余積が affine であることと、局所有限表示性の始域の局所性を使う。
規約：始域に affine 性・Noether 性・準分離性を追加しない。
使われ方：A07 の affine 始域の細分を一般の始域へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u

/-- 一般の始域の有限表示 v 被覆を、元の射への写像を保つ有限表示な affine v 被覆で細分する。 -/
theorem exists_affine_finitePresentation_vCover_refinement
    (R : Type u) [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFinitePresentation f] [QuasiCompact f] (hf : IsSchemeVCover f) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B), Algebra.FinitePresentation R B ∧
      ∃ k : Spec (CommRingCat.of B) ⟶ X,
        IsSchemeVCover (Spec.map (CommRingCat.ofHom (algebraMap R B))) ∧
        k ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  classical
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let 𝒰 := X.affineCover.finiteSubcover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec _))
  let T : Scheme.{u} := ∐ 𝒰.X
  letI : IsAffine T := by dsimp [T]; infer_instance
  let m : T ⟶ X := Sigma.desc 𝒰.f
  haveI : LocallyOfFinitePresentation (m ≫ f) := by
    apply IsZariskiLocalAtSource.of_openCover (P := @LocallyOfFinitePresentation)
      (sigmaOpenCover 𝒰.X)
    intro i
    change LocallyOfFinitePresentation (Sigma.ι 𝒰.X i ≫ m ≫ f)
    rw [← Category.assoc, Sigma.ι_comp_desc]
    infer_instance
  let B : Type u := Γ(T, ⊤)
  let k : Spec (CommRingCat.of B) ⟶ X := T.isoSpec.inv ≫ m
  let φ := Spec.preimage (k ≫ f)
  letI : Algebra R B := φ.hom.toAlgebra
  have heq : k ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    change k ≫ f = Spec.map φ
    exact (Spec.map_preimage (k ≫ f)).symm
  haveI : LocallyOfFinitePresentation (k ≫ f) := by
    dsimp only [k]
    rw [Category.assoc]
    infer_instance
  have hspec : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) :=
    heq ▸ (inferInstance : LocallyOfFinitePresentation (k ≫ f))
  have hfp : Algebra.FinitePresentation R B :=
    RingHom.finitePresentation_algebraMap.mp ((LocallyOfFinitePresentation.SpecMap_iff _).mp hspec)
  have hk : IsSchemeVCover k :=
    (isSchemeVCover_of_isIso T.isoSpec.inv).comp (isSchemeVCover_sigmaDesc_openCover 𝒰)
  refine ⟨B, inferInstance, inferInstance, hfp, k, ?_, heq⟩
  rw [← heq]
  exact hk.comp hf

end SerrePositivity.AlgebraicGeometry

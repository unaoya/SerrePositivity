module

public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelFinal
public import SerrePositivity.AlgebraicGeometry.CoefficientVCoverModelStages
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Ring.ULift

/-!
概要：任意の affine v 被覆を、有限型 F_p 上の実際の被覆模型の filtered 余極限に表す。
方針：同じ宇宙の ULift F_p 上の被覆模型を取り、各段の係数構造を環同型で戻す。
規約：元の f の有限表示性・R の Noether 性を要求せず、零環を許す。
使われ方：BS17 Lemma 2.12 の模型供給と、2g の有限型 F_p への帰着。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u

private theorem finiteType_primeField_arrow
    (p : ℕ) {A B : Type u} [CommRing A] [CommRing B]
    [Algebra (ULift.{u} (ZMod p)) A] [Algebra (ULift.{u} (ZMod p)) B]
    [Algebra.FiniteType (ULift.{u} (ZMod p)) A] [Algebra.FiniteType (ULift.{u} (ZMod p)) B]
    (f : A →+* B)
    (hf : f.comp (algebraMap (ULift.{u} (ZMod p)) A) = algebraMap (ULift.{u} (ZMod p)) B) :
    ∃ (_ : Algebra (ZMod p) A) (_ : Algebra (ZMod p) B),
      Algebra.FiniteType (ZMod p) A ∧ Algebra.FiniteType (ZMod p) B ∧
      f.comp (algebraMap (ZMod p) A) = algebraMap (ZMod p) B := by
  let e : ZMod p ≃+* ULift.{u} (ZMod p) := ULift.ringEquiv.symm
  let a := (algebraMap (ULift.{u} (ZMod p)) A).comp e.toRingHom
  let b := (algebraMap (ULift.{u} (ZMod p)) B).comp e.toRingHom
  have ha : a.FiniteType := (RingHom.finiteType_algebraMap.mpr inferInstance).comp
    (RingHom.FiniteType.of_surjective e.toRingHom e.surjective)
  have hb : b.FiniteType := (RingHom.finiteType_algebraMap.mpr inferInstance).comp
    (RingHom.FiniteType.of_surjective e.toRingHom e.surjective)
  refine ⟨a.toAlgebra, b.toAlgebra, ha, hb, ?_⟩
  exact congrArg (fun h ↦ h.comp e.toRingHom) hf

/-- BS17 Lemma 2.12 の模型供給：任意の affine v 被覆は有限型 F_p の被覆模型の実際の余極限。 -/
theorem exists_primeField_vCover_filtered_model
    (p : ℕ) [Fact p.Prime] (R C : Type u) [CommRing R] [CommRing C]
    [Algebra (ZMod p) R] (f : R →+* C) (hv : IsAffineVCover f) :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J) (F : J ⥤ Arrow CommRingCat.{u})
      (c : Cocone F), c.pt = Arrow.mk (CommRingCat.ofHom f) ∧ Nonempty (IsColimit c) ∧
      ∀ j, (∃ (_ : Algebra (ZMod p) (F.obj j).left) (_ : Algebra (ZMod p) (F.obj j).right),
        Algebra.FiniteType (ZMod p) (F.obj j).left ∧ Algebra.FiniteType (ZMod p) (F.obj j).right ∧
        (F.obj j).hom.hom.comp (algebraMap (ZMod p) (F.obj j).left) =
          algebraMap (ZMod p) (F.obj j).right) ∧
        IsNoetherianRing (F.obj j).left ∧ IsNoetherianRing (F.obj j).right ∧
        (F.obj j).hom.hom.FinitePresentation ∧ IsAffineVCover (F.obj j).hom.hom := by
  let K := ULift.{u} (ZMod p)
  let e : K ≃+* ZMod p := ULift.ringEquiv
  letI : IsNoetherianRing K := isNoetherianRing_of_ringEquiv (ZMod p) e.symm
  letI : Algebra K R := ((algebraMap (ZMod p) R).comp e.toRingHom).toAlgebra
  letI : Algebra K C := (f.comp ((algebraMap (ZMod p) R).comp e.toRingHom)).toAlgebra
  let g : R →ₐ[K] C := { __ := f, commutes' := fun _ ↦ rfl }
  let J := CoefficientVCoverModelIndex K g
  letI : IsFiltered J := isFiltered_coefficientVCoverModelIndex K g hv
  let F := coefficientVCoverModelSmallArrowDiagram K g
  let c := coefficientVCoverModelSmallArrowCocone K g
  refine ⟨J, inferInstance, inferInstance, F, c, rfl,
    ⟨coefficientVCoverModelSmallArrowCoconeIsColimit K g hv⟩, ?_⟩
  intro j
  exact ⟨finiteType_primeField_arrow p ((F.obj j).hom.hom)
      (coefficientVCoverModelSmallArrow_comp_algebraMap K g j),
    inferInstanceAs (IsNoetherianRing ((coefficientVCoverModelSmallArrowDiagram K g).obj j).left),
    inferInstanceAs (IsNoetherianRing ((coefficientVCoverModelSmallArrowDiagram K g).obj j).right),
    coefficientVCoverModelSmallArrow_finitePresentation K g j,
    coefficientVCoverModelSmallArrow_vCover K g j⟩

end SerrePositivity.AlgebraicGeometry

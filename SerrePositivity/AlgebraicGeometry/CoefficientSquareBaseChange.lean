module

public import SerrePositivity.AlgebraicGeometry.AffineVCover
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
概要：有限型係数模型の正方形から、元の基底上の実際の有限表示 v 被覆を作る。
方針：tensor の pushout を構成し、有限表示性を底変換し、v 判定を合成から消去する。
規約：元の R の Noether 性を要求せず、D→P→C の実際の射を保持する。
使われ方：B03・B04 の全模型から実際の被覆係数模型への射の供給。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
open scoped TensorProduct
universe u

/-- 全模型の正方形は、元の基底上の実際の有限表示 v 被覆を与える。 -/
theorem exists_finitePresentation_baseChange_of_coefficient_square
    (k A D R C : Type u) [CommRing k] [IsNoetherianRing k]
    [CommRing A] [CommRing D] [CommRing R] [CommRing C]
    [Algebra k A] [Algebra k D] [Algebra k R] [Algebra k C]
    [Algebra.FiniteType k A] [Algebra.FiniteType k D]
    (t : A →ₐ[k] D) (a : A →ₐ[k] R) (d : D →ₐ[k] C) (g : R →ₐ[k] C)
    (hsq : d.comp t = g.comp a) (hv : IsAffineVCover g.toRingHom) :
    ∃ (P : Type u) (_ : CommRing P) (_ : Algebra R P),
      Algebra.FinitePresentation R P ∧ IsAffineVCover (algebraMap R P) ∧
      ∃ (ι : D →+* P) (p : P →+* C),
        p.comp (algebraMap R P) = g.toRingHom ∧ p.comp ι = d.toRingHom ∧
        ι.comp t.toRingHom = (algebraMap R P).comp a.toRingHom := by
  letI : Algebra A R := a.toRingHom.toAlgebra
  letI : Algebra A D := t.toRingHom.toAlgebra
  letI : IsScalarTower k A R := IsScalarTower.of_algebraMap_eq' a.comp_algebraMap.symm
  letI : IsScalarTower k A D := IsScalarTower.of_algebraMap_eq' t.comp_algebraMap.symm
  letI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  letI : Algebra.FiniteType A D := Algebra.FiniteType.of_restrictScalars_finiteType k A D
  letI : Algebra.FinitePresentation A D := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let P := R ⊗[A] D
  have hfp : Algebra.FinitePresentation R P :=
    ((Algebra.Presentation.ofFinitePresentation A D).baseChange R).finitePresentation_of_isFinite
  let H := IsPushout.of_isColimit (CommRingCat.pushoutCoconeIsColimit A R D)
  have hw : CommRingCat.ofHom (algebraMap A R) ≫ CommRingCat.ofHom g.toRingHom =
      CommRingCat.ofHom (algebraMap A D) ≫ CommRingCat.ofHom d.toRingHom :=
    CommRingCat.hom_ext (congrArg AlgHom.toRingHom hsq.symm)
  let p : P →+* C := (H.desc (CommRingCat.ofHom g.toRingHom)
    (CommRingCat.ofHom d.toRingHom) hw).hom
  let ι : D →+* P := (Algebra.TensorProduct.includeRight : D →ₐ[A] P).toRingHom
  have hp : p.comp (algebraMap R P) = g.toRingHom :=
    congrArg CommRingCat.Hom.hom (H.inl_desc _ _ hw)
  have hi : p.comp ι = d.toRingHom := congrArg CommRingCat.Hom.hom (H.inr_desc _ _ hw)
  have hι : ι.comp t.toRingHom = (algebraMap R P).comp a.toRingHom :=
    (congrArg CommRingCat.Hom.hom H.w).symm
  have hvP : IsAffineVCover (algebraMap R P) := IsAffineVCover.of_comp (by rw [hp]; exact hv)
  exact ⟨P, inferInstance, inferInstance, hfp, hvP, ι, p, hp, hi, hι⟩

end SerrePositivity.AlgebraicGeometry

module

public import SerrePositivity.AlgebraicGeometry.EtaleSourceBoundaryFlat
public import SerrePositivity.AlgebraicGeometry.SmoothIntegralFlatCenter

/-!
概要：相対 Noether 正規化の有限局所模型に平坦化中心を作る。
方針：étale 局所模型に境界外の平坦性を移し、有限写像の先で加群を考えて次元帰納を使う。
規約：純変換は基底上の同じ加群で取る。
使われ方：Stacks 0815 で局所中心を 0814 の共通中心へ渡す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
/--
概要：相対次元を指定した有限な étale 局所模型に対し、より小さい次元の帰納仮定から平坦化中心が得られる。
方針：有限写像に沿って加群のスカラーを制限し、滑らかで幾何学的整な正規化先に平坦化を適用する。
規約：始域の環を正規化先へ有限にするだけで、始域の滑らかさは使わない。
使われ方：任意の有限型アフィン始域の étale 局所中心を構成する。
-/
theorem exists_affine_flatPure_center_of_finite_normalization
    {R B C E D : CommRingCat.{u}} [Algebra R B] [IsNoetherianRing R]
    (e : R ⟶ C) (f : C ⟶ E) (h : E ⟶ D) (j : B ⟶ D)
    (hc : e ≫ f ≫ h = CommRingCat.ofHom (algebraMap R B) ≫ j)
    (he : e.hom.Etale) (hj : j.hom.Etale) (hh : h.hom.Finite)
    (n : ℕ) (hsm : SmoothOfRelativeDimension n (Spec.map f))
    (hgi : GeometricallyIntegral (Spec.map f))
    {M : Type u} [AddCommGroup M] [Module R M] [Module B M]
    [IsScalarTower R B M] [Module.Finite B M]
    (a : R) (ha : IsRegular a) [Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] M)]
    (hrec : HasAffineFlatPureCentersBelow.{u} n) :
    letI : Algebra R C := e.hom.toAlgebra
    letI : Algebra B D := j.hom.toAlgebra
    letI : Algebra C D := (f ≫ h).hom.toAlgebra
    ∃ I : Ideal C, I.FG ∧ PrimeSpectrum.basicOpen (e.hom a) ≤ affineCenterComplement I ∧
      HasFlatPurePullbacks (affineBlowupπ I) (e.hom a) (D ⊗[B] M) := by
  let : Algebra R C := e.hom.toAlgebra
  let : Algebra C E := f.hom.toAlgebra
  let : Algebra E D := h.hom.toAlgebra
  let : Algebra C D := (f ≫ h).hom.toAlgebra
  let : Algebra R D := (e ≫ f ≫ h).hom.toAlgebra
  let : Algebra B D := j.hom.toAlgebra
  let : IsScalarTower R C D := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower C E D := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R B D :=
    IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom hc)
  let : Algebra.Etale R C := he
  let : Algebra.Etale B D := hj
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing R C
  let : SmoothOfRelativeDimension n (Spec.map f) := hsm
  let : Smooth (Spec.map f) := SmoothOfRelativeDimension.smooth n _
  let : GeometricallyIntegral (Spec.map f) := hgi
  let : Module.Flat C E := (Flat.SpecMap_iff (f := f)).mp inferInstance
  let : Algebra.FiniteType C E :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
      (inferInstance : LocallyOfFiniteType (Spec.map f))
  let : Module.Finite E D := hh
  let N := D ⊗[B] M
  let : Module.Finite E N := Module.Finite.trans D N
  let : Module.Flat (Localization.Away (e.hom a)) (Localization.Away (e.hom a) ⊗[C] N) :=
    flat_away_tensor_of_etale_source_base_change (D := D) a
  exact exists_affine_flatPure_center_of_smooth_geometricallyIntegral
    (B := E) (M := N) n (e.hom a) (algebraMap_isRegular_of_flat R C a ha) hrec

end SerrePositivity.AlgebraicGeometry

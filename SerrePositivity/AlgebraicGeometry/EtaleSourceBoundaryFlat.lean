module

public import SerrePositivity.AlgebraicGeometry.EtaleSourceBaseChangeFlat
public import SerrePositivity.CommutativeAlgebra.Localization.EtaleAway

/-!
概要：始域と基底の étale 局所模型に、境界外の相対平坦性を移す。
方針：境界を四隅で反転し、局所化の押し出しと étale 四角形の平坦性を使う。
規約：始域の加群は基底上で有限である必要はない。
使われ方：Stacks 0815 で相対 Noether 正規化後に余核の次元帰納を始める。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped TensorProduct

private theorem away_pushout {R B A T : Type*} [CommRing R] [CommRing B]
    [CommRing A] [CommRing T] [Algebra R B] [Algebra R A] [Algebra B T]
    [Algebra R T] [Algebra A T] [IsScalarTower R B T] [IsScalarTower R A T]
    (a : R) [IsLocalization.Away a A] [IsLocalization.Away (algebraMap R B a) T] :
    Algebra.IsPushout R A B T := by
  let : IsLocalization (Algebra.algebraMapSubmonoid B (.powers a)) T := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  exact (Algebra.IsPushout.comm R B A T).mp
    (Algebra.isPushout_of_isLocalization (.powers a) A B T)

set_option backward.isDefEq.respectTransparency false in
/--
概要：境界外で平坦な加群は、基底と始域をそれぞれ étale に変更しても境界外で平坦。
方針：境界を可逆にした四角形で平坦性を移し、二段テンソル積を打ち消す。
規約：基底の境界は一つの主開で表す。
使われ方：次元を制御した étale 局所有限化の加群を相対正規化先に押し出す直前。
-/
theorem flat_away_tensor_of_etale_source_base_change
    {R C B D M : Type u} [CommRing R] [CommRing C] [CommRing B] [CommRing D]
    [Algebra R C] [Algebra R B] [Algebra R D] [Algebra C D] [Algebra B D]
    [IsScalarTower R C D] [IsScalarTower R B D] [Algebra.Etale R C] [Algebra.Etale B D]
    [AddCommGroup M] [Module R M] [Module B M] [IsScalarTower R B M]
    (a : R) [Module.Flat (Localization.Away a) (Localization.Away a ⊗[R] M)] :
    let L := Localization.Away (algebraMap R C a)
    Module.Flat L (L ⊗[C] (D ⊗[B] M)) := by
  let A := Localization.Away a
  let b := algebraMap R B a
  let c := algebraMap R C a
  let H := Localization.Away b
  let L := Localization.Away c
  let T := Localization.Away (algebraMap R D a)
  let : Algebra A H := SerrePositivity.GenericEtale.awayAlgebra R B a
  let : Algebra A L := SerrePositivity.GenericEtale.awayAlgebra R C a
  let : Algebra A T := SerrePositivity.GenericEtale.awayAlgebra R D a
  let : IsScalarTower R A H := SerrePositivity.GenericEtale.awayAlgebra_scalarTower R B a
  let : IsScalarTower R A L := SerrePositivity.GenericEtale.awayAlgebra_scalarTower R C a
  let : IsScalarTower R A T := SerrePositivity.GenericEtale.awayAlgebra_scalarTower R D a
  let : IsScalarTower R B T := .to₁₂₄ R B D T
  let : IsScalarTower R C T := .to₁₂₄ R C D T
  have hB : IsUnit (algebraMap B T b) := by
    change IsUnit (algebraMap B T (algebraMap R B a))
    rw [← IsScalarTower.algebraMap_apply R B T, IsScalarTower.algebraMap_apply R D T]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R D a)
  have hC : IsUnit (algebraMap C T c) := by
    change IsUnit (algebraMap C T (algebraMap R C a))
    rw [← IsScalarTower.algebraMap_apply R C T, IsScalarTower.algebraMap_apply R D T]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap R D a)
  let : Algebra H T := (IsLocalization.Away.lift b hB).toAlgebra
  let : Algebra L T := (IsLocalization.Away.lift c hC).toAlgebra
  let : IsScalarTower B H T := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.Away.lift_comp b hB).symm
  let : IsScalarTower C L T := IsScalarTower.of_algebraMap_eq'
    (IsLocalization.Away.lift_comp c hC).symm
  let : IsScalarTower R H T := IsScalarTower.of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq R B H, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq B H T, ← IsScalarTower.algebraMap_eq R B T]
  let : IsScalarTower R L T := IsScalarTower.of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq R C L, ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq C L T, ← IsScalarTower.algebraMap_eq R C T]
  let : IsScalarTower A H T := IsScalarTower.of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext (.powers a)
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R A H,
      ← IsScalarTower.algebraMap_eq R H T, ← IsScalarTower.algebraMap_eq R A T]
  let : IsScalarTower A L T := IsScalarTower.of_algebraMap_eq' <| by
    apply IsLocalization.ringHom_ext (.powers a)
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R A L,
      ← IsScalarTower.algebraMap_eq R L T, ← IsScalarTower.algebraMap_eq R A T]
  let : Algebra.Etale R A := Algebra.Etale.of_isLocalizationAway a
  let : Algebra.Etale B H := Algebra.Etale.of_isLocalizationAway b
  let : Algebra.Etale C L := Algebra.Etale.of_isLocalizationAway c
  let : Algebra.Etale R L := Algebra.Etale.comp R C L
  let : Algebra.Etale A L := Algebra.Etale.of_restrictScalars R A L
  let : Algebra.Etale D T := Algebra.Etale.of_isLocalizationAway (algebraMap R D a)
  let : Algebra.Etale B T := Algebra.Etale.comp B D T
  let : Algebra.Etale H T := Algebra.Etale.of_restrictScalars B H T
  let : Algebra.IsPushout R A B H := away_pushout a
  let N := H ⊗[B] M
  let : Module.Flat A N := Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange R A B H M)
  let : Module.Flat L (T ⊗[H] N) := flat_tensor_of_etale_source_base_change (R := A) (C := L)
  let e₁ := TensorProduct.AlgebraTensorModule.cancelBaseChange B H T T M
  let : IsLocalization.Away (algebraMap C D c) T := by
    change IsLocalization.Away (algebraMap C D (algebraMap R C a)) T
    rw [← IsScalarTower.algebraMap_apply R C D]
    infer_instance
  let : Algebra.IsPushout C L D T := away_pushout c
  let e₂ := Algebra.IsPushout.cancelBaseChange C L D T (D ⊗[B] M)
  let e₃ := TensorProduct.AlgebraTensorModule.cancelBaseChange B D T T M
  exact Module.Flat.of_linearEquiv (((e₁.trans e₃.symm).restrictScalars L).trans e₂).symm

end SerrePositivity.AlgebraicGeometry

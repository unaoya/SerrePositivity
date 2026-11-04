module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericModel
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.GenericEtale

/-!
# 一般点の部分代数のエタール性を広げる

## 概要
局所化後のエタール部分代数の逆像は、一つの分母を反転すればエタール。

## 方針
逆像モデルの有限性と局所化の同定を使い、余接加群の消滅を延長する。

## 規約
反転する元は基底の指定された乗法集合から選ぶ。

## 使われ方
一般点の有限エタール分解を主開集合に広げる最初の段階。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

/-- 一般点でエタールな部分代数の有限モデルは、一つの分母でエタールになる。 -/
theorem exists_away_etale_genericSubalgebraModel
    {R K A B : Type u} [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra R B] [Algebra K B] [IsScalarTower R K B]
    [IsNoetherianRing R] [Module.Finite R A]
    (M : Submonoid R) [IsLocalization M K]
    (f : A →ₐ[R] B) [IsLocalizedModule M f.toLinearMap]
    (C : Subalgebra K B) [Algebra.Etale K C] :
    ∃ g : M, Algebra.Etale R
      (Localization.Away (algebraMap R (genericSubalgebraModel f C) g)) := by
  let T := genericSubalgebraModel f C
  let t := genericSubalgebraModelMap f C
  let : Module.Finite R T := genericSubalgebraModel_finite f C
  let : Algebra T C := t.toRingHom.toAlgebra
  let : IsScalarTower R T C := IsScalarTower.of_algebraMap_eq fun r ↦ (t.commutes r).symm
  let : IsLocalizedModule M t.toLinearMap := genericSubalgebraModel_isLocalizedModule M f C
  let : IsLocalization (Algebra.algebraMapSubmonoid T M) C :=
    isLocalizedModule_iff_isLocalization.mp (show IsLocalizedModule M
      (IsScalarTower.toAlgHom R T C).toLinearMap from inferInstanceAs (IsLocalizedModule M t.toLinearMap))
  let : Algebra.FormallyEtale R K := Algebra.FormallyEtale.of_isLocalization M
  let : Algebra.FormallyEtale R C := Algebra.FormallyEtale.comp R K C
  let : Algebra.FinitePresentation R T := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact exists_away_etale_of_localized_formallyEtale R T C M

end SerrePositivity.CommutativeAlgebra

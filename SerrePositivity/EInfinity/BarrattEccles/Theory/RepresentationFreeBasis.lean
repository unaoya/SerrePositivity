module

public import Mathlib.RepresentationTheory.Rep.Iso
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# 自由軌道の基底を持つ表現

## 概要
HA 3.2.4.7 の二色比較に使う、自由軌道の基底から自由表現への指定同型。

## 方針
単位群成分の基底を自由表現から延長し、全基底上で線形同型と照合する。

## 規約
群は基底の第二成分に左乗法で作用する。

## 使われ方
二色の係数複体のテンソル側の次数ごとの射影性。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory
variable {A G I : Type u} [CommRing A] [Group G]

/-- 自由軌道の基底からの自由表現の射は、指定した基底同型に一致する。 -/
lemma representationFreeBasisMap_eq (V : Rep.{u} A G)
    (b : Module.Basis (I × G) A V)
    (hb : ∀ g i h, V.ρ g (b (i, h)) = b (i, g * h)) :
    (Rep.freeLift A G V (fun i => b (i, 1))).hom.toLinearMap =
      ((Finsupp.basis (fun _ : I => MonoidAlgebra.basis G A)).equiv b
        (Equiv.sigmaEquivProd _ _)).toLinearMap := by
  apply (Finsupp.basis (fun _ : I => MonoidAlgebra.basis G A)).ext
  rintro ⟨i, g⟩
  rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply]
  simp only [Finsupp.coe_basis, MonoidAlgebra.basis_apply]
  change Representation.freeLift V.ρ (fun i => b (i, 1))
    (Finsupp.single i (MonoidAlgebra.single g 1)) = b (i, g)
  rw [Representation.freeLift_single_single, one_smul, hb, mul_one]

/-- 自由軌道の基底を持つ表現は、その軌道の集合上の自由表現である。 -/
def representationFreeBasisIso (V : Rep.{u} A G)
    (b : Module.Basis (I × G) A V)
    (hb : ∀ g i h, V.ρ g (b (i, h)) = b (i, g * h)) :
    Rep.free A G I ≅ V := by
  let f := Rep.freeLift A G V (fun i => b (i, 1))
  let F := forget (Rep A G)
  haveI : IsIso (F.map f) := by
    apply (CategoryTheory.isIso_iff_bijective _).mpr
    change Function.Bijective f.hom.toLinearMap
    rw [show f.hom.toLinearMap = _ from representationFreeBasisMap_eq V b hb]
    exact ((Finsupp.basis (fun _ : I => MonoidAlgebra.basis G A)).equiv b
      (Equiv.sigmaEquivProd _ _)).bijective
  letI : IsIso f := isIso_of_reflects_iso f F
  exact asIso f

end SerrePositivity.EInfinity

module

public import SerrePositivity.KST.DerivedBlowup.ExteriorAugmentationBoundary

/-!
概要：KST Def3.1 の標準添加射を単位の像から一意に特徴付ける。
方針：次数0の単位成分が可逆なので、単一複体への射を単位で比較する。
規約：単一複体への鎖写像としての一意性。目標の係数構造を固定する。
使われ方：dg 関手として構成した添加と明示的な添加鎖写像との一致。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory HomologicalComplex

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- 概要：標準添加射は単位から入った係数を構造射で送る。
方針：標準添加の次数0公式と Koszul 単位の総外積での係数公式を使う。
規約：KST Def3.1。使われ方：単位保存による添加の一意性。 -/
theorem exteriorKoszulAugmentation_unit_zero (d : M →ₗ[R] R)
    (hd : ∀ m, algebraMap R S (d m) = 0) (r : R) :
    ((exteriorKoszulUnit d ≫ exteriorKoszulAugmentation d hd).f 0)
      ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv r) =
        (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R S)).inv (algebraMap R S r) := by
  simp only [exteriorKoszulAugmentation, mkHomToSingle_f, comp_f, ModuleCat.comp_apply]
  congr 1
  change exteriorAugmentation (S := S)
    (exteriorCochainInclusion d 0 ((exteriorKoszulUnit d).f 0 r)) = _
  rw [exteriorKoszulUnit_inclusion]
  exact (exteriorAugmentation (R := R) (M := M) (S := S)).commutes r

/-- 概要：単位の1を1へ送る単一複体への鎖写像は標準添加射に等しい。
方針：次数0単位の可逆性で左消去し、R からの線形射を1で比較する。
規約：KST Def3.1。使われ方：標準添加 dg 関手の Hom 写像の同定。 -/
theorem exteriorKoszulAugmentation_unique (d : M →ₗ[R] R)
    (hd : ∀ m, algebraMap R S (d m) = 0)
    (g : exteriorKoszulCochain d ⟶ (single _ (.up ℤ) 0).obj (ModuleCat.of R S))
    (hu : ((exteriorKoszulUnit d ≫ g).f 0)
      ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)).inv (1 : R)) =
        (singleObjXSelf (.up ℤ) 0 (ModuleCat.of R S)).inv (1 : S)) :
    g = exteriorKoszulAugmentation d hd := by
  apply to_single_hom_ext
  have := exteriorKoszulUnit_f_zero_isIso d
  apply (cancel_epi ((exteriorKoszulUnit d).f 0)).mp
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  have h := exteriorKoszulAugmentation_unit_zero d hd (1 : R)
  rw [map_one (algebraMap R S)] at h
  exact hu.trans h.symm

end SerrePositivity.KST.DerivedBlowup

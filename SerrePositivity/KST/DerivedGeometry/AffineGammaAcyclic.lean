module

public import SerrePositivity.KST.DerivedGeometry.AffineCoefficientCohomology
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-!
概要：アフィン係数大域切断を H 加群へ取る実際の関手の準連接層における非輪状性。
方針：元の係数加群層圏の injective 分解で計算し、係数大域環から H への完全な制限を使う。
規約：H の可換性・平坦性を仮定しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数アフィン導来比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits AlgebraicGeometry PrimeSpectrum Abelian
namespace SerrePositivity.KST.DerivedGeometry
variable {A : CommRingCat.{u}} (H : Type u) [Ring H] [Algebra A H]

/-- 概要：H 加群値の係数大域切断は加法的。方針：評価と係数制限の加法性を合成する。
規約：平坦性は不要。使われ方：TT §3、Toën §3.2 の右導来大域切断。 -/
instance affineCoefficientΓ_additive : (affineCoefficientΓ (R := A) H).Additive where
  map_add := by intros; rfl

/-- 概要：H 加群値の係数大域切断は有限極限を保つ。方針：評価と制限の極限保存を合成する。
規約：全層での右完全性は仮定しない。使われ方：TT §3、Toën §3.2 の右導来随伴。 -/
instance affineCoefficientΓ_preservesFiniteLimits :
    PreservesFiniteLimits (affineCoefficientΓ (R := A) H) := by
  change PreservesFiniteLimits (ringedModuleSections (TopCat.of (PrimeSpectrum A))
    (tensorCoefficientSheaf H (Scheme.ΓSpecIso A).inv.hom).ring ⊤ ⋙
      ModuleCat.restrictScalars
        ((tensorCoefficientConstant H (Scheme.ΓSpecIso A).inv.hom).app (.op ⊤)).hom)
  have : PreservesFiniteLimits (ringedModuleSections (TopCat.of (PrimeSpectrum A))
      (tensorCoefficientSheaf H (Scheme.ΓSpecIso A).inv.hom).ring ⊤) :=
    ringedModuleSections_preservesFiniteLimits _ _ _
  exact comp_preservesFiniteLimits _ _

/--
概要：準連接係数加群層では実際の H 加群値の右導来大域切断の正次数が零。
方針：同じ injective 分解の切断複体の完全性を大域環から H への制限で保つ。
規約：元の係数加群層圏の分解で計算し、H の平坦性は不要。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数 tilde の非輪状性。
-/
lemma affineCoefficientΓ_rightDerived_isZero
    (F : (tensorCoefficientSheaf H (Scheme.ΓSpecIso A).inv.hom).QCoh) (n : ℕ) :
    IsZero (((affineCoefficientΓ (R := A) H).rightDerived (n + 1)).obj F.obj) := by
  let B := tensorCoefficientSheaf H (Scheme.ΓSpecIso A).inv.hom
  let X := TopCat.of (PrimeSpectrum A)
  let I : InjectiveResolution (C := B.Modules) F.obj := ringedInjectiveResolution X B.ring F.obj
  have hs := ringedInjectiveSections_exactAt_of_ext_subsingleton X B.ring F.obj ⊤ n
    (affineCoefficient_globalExt_subsingleton B F n)
  have ht : (((affineCoefficientΓ (R := A) H).mapHomologicalComplex (.up ℕ)).obj I.cocomplex).ExactAt
      (n + 1) :=
    hs.map (ModuleCat.restrictScalars
      ((tensorCoefficientConstant H (Scheme.ΓSpecIso A).inv.hom).app (.op ⊤)).hom)
  exact IsZero.of_iso ht.isZero_homology (I.isoRightDerivedObj (affineCoefficientΓ (R := A) H) (n + 1))

end SerrePositivity.KST.DerivedGeometry

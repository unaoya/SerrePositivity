module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# 元の射影加群からのホモロジー写像の実現

## 概要
射影加群から元の複体のホモロジーへの写像を、同じ次数の single からの複体の射で実現する。

## 方針
元のホモロジー射影に沿って余輪体へ持ち上げ、元の single の射の構成子を使う。

## 規約
ホモロジー上の値は元の指定写像と一致させる。K-flat 性は仮定しない。

## 使われ方
BS Proposition 6.2 で元の affine line の零次・一次 HT 写像を実現する。
-/

public noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R]
variable {ι : Type v} [DecidableEq ι] {c : ComplexShape ι}
variable (K : HomologicalComplex (ModuleCat.{u} R) c) (i : ι)
variable (M : ModuleCat.{u} R) [Projective M]

/-- 元の射影加群からの指定ホモロジー写像は、同じ single からの射で実現できる。 -/
theorem exists_single_homology_lift (η : M ⟶ K.homology i) :
    ∃ q : (HomologicalComplex.single (ModuleCat.{u} R) c i).obj M ⟶ K,
      (HomologicalComplex.singleObjHomologySelfIso c i M).inv ≫
        HomologicalComplex.homologyMap q i = η := by
  let v := Projective.factorThru η (K.homologyπ i)
  let φ := v ≫ K.iCycles i
  have hφ (j : ι) (_ : c.Rel i j) : φ ≫ K.d i j = 0 := by
    dsimp only [φ]
    rw [Category.assoc, HomologicalComplex.iCycles_d, comp_zero]
  let q := HomologicalComplex.mkHomFromSingle φ hφ
  refine ⟨q, ?_⟩
  have hc : (HomologicalComplex.singleObjCyclesSelfIso c i M).inv ≫
      HomologicalComplex.cyclesMap q i = v := by
    apply (cancel_mono (K.iCycles i)).mp
    dsimp only [q]
    rw [Category.assoc, HomologicalComplex.cyclesMap_i, ← Category.assoc,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles,
      HomologicalComplex.mkHomFromSingle_f]
    simp only [φ, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ,
    Category.assoc, HomologicalComplex.homologyπ_naturality, ← Category.assoc, hc]
  exact Projective.factorThru_comp η (K.homologyπ i)

end SerrePositivity.BhattScholze.Prismatic.HTUniversalComparison

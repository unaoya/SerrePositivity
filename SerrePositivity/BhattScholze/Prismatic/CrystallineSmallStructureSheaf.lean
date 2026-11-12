module

public import SerrePositivity.BhattScholze.Prismatic.CrystallineStructureGluing
public import SerrePositivity.BhattScholze.Prismatic.CrystallineSmallSiteTopology
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Limits.Over
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSmallSiteTopology
import all SerrePositivity.BhattScholze.Prismatic.CrystallineStructureGluing
import all SerrePositivity.BhattScholze.Prismatic.CrystallineSiteBasic
import all Mathlib.CategoryTheory.EssentiallySmall
import all Mathlib.CategoryTheory.Opposites

/-!
# 小さい affine 結晶サイトの構造層

## 概要
構造環の前層は小さい結晶サイト上でも基底環の下の可換環の層となる。

## 方針
小さい模型の位相を大きいサイトからの誘導位相で抑え、型値の層性を移す。
環と基底環上の構造は忘却関手による極限の反映で戻す。

## 規約
通常の環値の層条件のみを扱い、導来大域切断には進まない。

## 使われ方
Berthelot III.4、Stacks 07JJ の構造層の場合。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k : Type u} [CommRing k] {J : Ideal k} (γ : DividedPowers J)
variable (R : Type u) [CommRing R] [Algebra (k ⧸ J) R] (κ : Cardinal.{u})

/-- 小さいサイトの生成位相は大きいサイトからの誘導位相に含まれる。 -/
theorem crystallineSmallTopology_le_induced :
    zariskiTopology p γ R κ ≤
      (equivSmallModel (CrysOver p γ R κ)).inverse.op.inducedTopology
        crystallineLargeZariskiTopology := by
  apply sInf_le
  intro ι hι X Y f hf
  rw [Functor.mem_inducedTopology_iff_of_isCoverDense,
    ← Sieve.generate_map_eq_functorPushforward, Presieve.map_ofArrows]
  exact crystallineLargeZariskiTopology_cover _ _ hf

/-- 小さい結晶サイトの構造前層の台集合は層。 -/
theorem crystallineSmallStructureTypes_isSheaf (hκ : Cardinal.aleph0 ≤ κ) :
    Presieve.IsSheaf (zariskiTopology p γ R κ)
      (crystallineStructureRing p γ R κ ⋙ Under.forget (CommRingCat.of k) ⋙
        forget CommRingCat) := by
  let E := (equivSmallModel (CrysOver p γ R κ)).inverse.op
  have H := E.op_comp_isSheaf_of_types (E.inducedTopology crystallineLargeZariskiTopology)
    crystallineLargeZariskiTopology
    ⟨crystallineLargeStructureTypes,
      (isSheaf_iff_isSheaf_of_type _ _).mpr (crystallineLargeStructureTypes_isSheaf hκ)⟩
  apply Presieve.isSheaf_of_le _ (crystallineSmallTopology_le_induced p γ R κ)
  exact H

/-- affine 結晶サイトの構造環は基底環の下の可換環の層。 -/
theorem crystallineStructure_isSheaf (hκ : Cardinal.aleph0 ≤ κ) :
    Presheaf.IsSheaf (zariskiTopology p γ R κ) (crystallineStructureRing p γ R κ) := by
  letI : Limits.ReflectsLimitsOfSize.{u, u}
      (Under.forget (CommRingCat.of k) ⋙ forget CommRingCat) :=
    Limits.reflectsLimits_of_reflectsIsomorphisms
  apply Presheaf.isSheaf_of_isSheaf_comp _ _
    (Under.forget (CommRingCat.of k) ⋙ forget CommRingCat)
  exact (isSheaf_iff_isSheaf_of_type _ _).mpr
    (crystallineSmallStructureTypes_isSheaf p γ R κ hκ)

end SerrePositivity.BhattScholze.Prismatic

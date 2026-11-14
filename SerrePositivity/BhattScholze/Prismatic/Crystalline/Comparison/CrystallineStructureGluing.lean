module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineZariskiCoverage
public import SerrePositivity.CommutativeAlgebra.Localization.AwayGluing
public import Mathlib.CategoryTheory.Sites.IsSheafFor
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineLocalizationLift
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteLocalization
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic
import all Mathlib.CategoryTheory.Opposites

/-!
# 結晶主開被覆での構造環の貼り合わせ

## 概要
構造環の切断は結晶主開被覆上の両立する切断から一意に貼り合わさる。

## 方針
共通主開の結晶厚化への延長を用いて、環の主開貼り合わせへ帰着する。

## 規約
まず型値の構造前層について証明する。環と基底環上の構造は後で戻す。

## 使われ方
Berthelot III.4、Stacks 07JJ の構造層の場合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R] {κ : Cardinal.{u}}

/-- 結晶厚化の台集合を取る関手。 -/
def crysUnderlying : CrysOver p γ R κ ⥤ Type u where
  obj X := X.B
  map f := TypeCat.ofHom f.toAlgHom

/-- 大きい結晶サイトの構造前層の台集合。 -/
def crystallineLargeStructureTypes : (CrysOver p γ R κ)ᵒᵖᵒᵖ ⥤ Type u :=
  unopUnop _ ⋙ crysUnderlying

/-- 結晶主開被覆上の両立する構造環の切断は一意に貼り合わさる。 -/
theorem crystallineLargeStructure_glue (hκ : Cardinal.aleph0 ≤ κ)
    {ι : Type u} [Finite ι] {X : CrysOver p γ R κ}
    (Y : ι → CrysOver p γ R κ) (f : ∀ i, X ⟶ Y i)
    (hf : CrysOver.IsZariskiFamily Y f) :
    Presieve.IsSheafFor crystallineLargeStructureTypes
      (Presieve.ofArrows (fun i => Opposite.op (Y i)) (fun i => (f i).op)) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  obtain ⟨b, hb, hl⟩ := hf
  letI : ∀ i, Algebra X.B (Y i).B := fun i => (f i).toAlgHom.toRingHom.toAlgebra
  letI : ∀ i, IsLocalization.Away (b i) (Y i).B := fun i => (hl i).1
  apply SerrePositivity.CommutativeAlgebra.Localization.existsUnique_glue_away b
    (fun i => (Y i).B) hb x
  intro d i j hi hj
  let a : X ⟶ crysAway X d hκ := crysAwayHom X d hκ
  let li : Y i ⟶ crysAway X d hκ :=
    crysLocalizationLift (f i) (b i) (hl i).1 (hl i).2 a hi
  let lj : Y j ⟶ crysAway X d hκ :=
    crysLocalizationLift (f j) (b j) (hl j).1 (hl j).2 a hj
  have he : li.op ≫ (f i).op = lj.op ≫ (f j).op := by
    apply Quiver.Hom.unop_inj
    exact (crysLocalizationLift_comp (f i) (b i) (hl i).1 (hl i).2 a hi).trans
      (crysLocalizationLift_comp (f j) (b j) (hl j).1 (hl j).2 a hj).symm
  exact hx i j (Opposite.op (crysAway X d hκ)) li.op lj.op he

/-- 大きい結晶サイトで構造前層の台集合は層。 -/
theorem crystallineLargeStructureTypes_isSheaf (hκ : Cardinal.aleph0 ≤ κ) :
    Presieve.IsSheaf crystallineLargeZariskiTopology
      (crystallineLargeStructureTypes (p := p) (γ := γ) (R := R) (κ := κ)) := by
  rw [← crystallineZariskiCoverage_toGrothendieck hκ, Presieve.isSheaf_coverage]
  rintro X S ⟨ι, hι, Y, f, hf, rfl⟩
  exact crystallineLargeStructure_glue hκ Y f hf

end SerrePositivity.BhattScholze.Prismatic

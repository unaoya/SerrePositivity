module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteZariski

/-!
# 分冪基底の射に沿う結晶厚化の制限

## 概要
分冪基底射に沿って係数を制限し、同じ結晶厚化を元の基底の上で読む。

## 方針
台環・分冪・剰余構造射は固定し、基底の射を合成する。

## 規約
剰余代数の二つの係数構造の両立を環射の等式として要求する。

## 使われ方
Berthelot III.4、Stacks 07HM。第0 Witt 成分による結晶サイトの基底の制限。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable (p : ℕ) {k l : Type u} [CommRing k] [CommRing l]
variable {J : Ideal k} {J' : Ideal l} (γ : DividedPowers J) (ε : DividedPowers J')
variable (R : Type u) [CommRing R] [Algebra (k ⧸ J) R] [Algebra (l ⧸ J') R]
variable (κ : Cardinal.{u}) (g : k →+* l) (hg : DividedPowers.IsDPMorphism γ ε g)
variable (hR : (algebraMap (l ⧸ J') R).comp ((Ideal.Quotient.mk J').comp g) =
  (algebraMap (k ⧸ J) R).comp (Ideal.Quotient.mk J))

/-- 分冪基底の射に沿う制限は同じ台環・剰余構造射を持つ。 -/
def crysBaseRestriction : CrysOver p ε R κ ⥤ CrysOver p γ R κ where
  obj X := by
    let : Algebra k X.B := ((algebraMap l X.B).comp g).toAlgebra
    exact {
      B := X.B
      JB := X.JB
      δ := X.δ
      base_dp := X.base_dp.comp _ hg
      nilpotent := X.nilpotent
      sec := X.sec
      sec_comp := by
        ext a
        change X.sec (algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a)) =
          Ideal.Quotient.mk X.JB (algebraMap l X.B (g a))
        have hr : algebraMap (l ⧸ J') R (Ideal.Quotient.mk J' (g a)) =
            algebraMap (k ⧸ J) R (Ideal.Quotient.mk J a) :=
          DFunLike.congr_fun hR a
        rw [← hr]
        exact DFunLike.congr_fun X.sec_comp (g a)
      small := X.small }
  map f := {
    toAlgHom := {
      toFun := f.toAlgHom
      __ := f.toAlgHom.toRingHom
      commutes' := fun a => f.toAlgHom.commutes (g a) }
    dp := f.dp
    comm_sec := f.comm_sec }
  map_id X := CrysOver.Hom.ext p rfl
  map_comp f h := CrysOver.Hom.ext p rfl

/-- 基底制限は、与えられた主開 Zariski 被覆を保つ。 -/
theorem crysBaseRestriction_isZariskiFamily {ι : Type u} [Finite ι]
    {X : CrysOver p ε R κ} {Y : ι → CrysOver p ε R κ} {f : ∀ i, X ⟶ Y i}
    (h : CrysOver.IsZariskiFamily Y f) :
    CrysOver.IsZariskiFamily (fun i => (crysBaseRestriction p γ ε R κ g hg hR).obj (Y i))
      (fun i => (crysBaseRestriction p γ ε R κ g hg hR).map (f i)) := h

end SerrePositivity.BhattScholze.Prismatic

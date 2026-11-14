module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteLocalization
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineResidue
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Site.CrystallineSiteBasic
import all Mathlib.RingTheory.Localization.Away.Basic

/-!
# 結晶厚化の局所化の普遍性

## 概要
台環が主開局所化で分冪イデアルが像である射は、厚化の圏でも局所化の普遍性を持つ。

## 方針
環の局所化の射を作り、分冪性を元の環からの合成で判定する。
剰余構造射の可換性は商の代表元で確認する。

## 規約
標準局所化に限らず、同じ元を局所化する任意の厚化を扱う。

## 使われ方
Berthelot III.4、Stacks 07HN。Zariski 被覆の引き戻しと共通主開への射。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace SerrePositivity.BhattScholze.Prismatic
variable {p : ℕ} {k : Type u} [CommRing k] {J : Ideal k} {γ : DividedPowers J}
variable {R : Type u} [CommRing R] [Algebra (k ⧸ J) R] {κ : Cardinal.{u}}
variable {X Y Z : CrysOver p γ R κ}

/-- 指定した元を単元に写す厚化の射は、主開局所化を通って延長する。 -/
def crysLocalizationLift (f : X ⟶ Y) (a : X.B)
    (hloc : letI := f.toAlgHom.toRingHom.toAlgebra; IsLocalization.Away a Y.B)
    (hI : Y.JB = X.JB.map f.toAlgHom.toRingHom)
    (g : X ⟶ Z) (hu : IsUnit (g.toAlgHom a)) : Y ⟶ Z := by
  letI : Algebra X.B Y.B := f.toAlgHom.toRingHom.toAlgebra
  letI : IsLocalization.Away a Y.B := hloc
  let φ : Y.B →+* Z.B := IsLocalization.Away.lift a (g := g.toAlgHom.toRingHom) hu
  have hφ : φ.comp f.toAlgHom.toRingHom = g.toAlgHom.toRingHom :=
    IsLocalization.Away.lift_comp a hu
  have hdp : Y.δ.IsDPMorphism Z.δ φ := by
    apply DividedPowers.IsDPMorphism.of_comp X.δ Y.δ Z.δ f.toAlgHom.toRingHom φ hI f.dp
    rw [hφ]
    exact g.dp
  refine {
    toAlgHom := {
      toFun := φ
      __ := φ
      commutes' := ?_ }
    dp := hdp
    comm_sec := ?_ }
  · intro r
    change φ (algebraMap k Y.B r) = algebraMap k Z.B r
    rw [← f.toAlgHom.commutes r]
    exact (DFunLike.congr_fun hφ (algebraMap k X.B r)).trans (g.toAlgHom.commutes r)
  · intro r y hy
    obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (X.sec r)
    have hyx : Ideal.Quotient.mk Y.JB y = Ideal.Quotient.mk Y.JB (f.toAlgHom x) :=
      hy.trans (f.comm_sec r x hx).symm
    have h := congrArg (Ideal.quotientMap Z.JB φ
      (Ideal.map_le_iff_le_comap.mp hdp.ideal_comp)) hyx
    change Ideal.Quotient.mk Z.JB (φ y) = Ideal.Quotient.mk Z.JB (φ (f.toAlgHom x)) at h
    have hφx : φ (f.toAlgHom x) = g.toAlgHom x := DFunLike.congr_fun hφ x
    rw [hφx] at h
    exact h.trans (g.comm_sec r x hx)

/-- 局所化を通る延長の合成は元の厚化の射。 -/
theorem crysLocalizationLift_comp (f : X ⟶ Y) (a : X.B)
    (hloc : letI := f.toAlgHom.toRingHom.toAlgebra; IsLocalization.Away a Y.B)
    (hI : Y.JB = X.JB.map f.toAlgHom.toRingHom)
    (g : X ⟶ Z) (hu : IsUnit (g.toAlgHom a)) :
    f ≫ crysLocalizationLift f a hloc hI g hu = g := by
  letI : Algebra X.B Y.B := f.toAlgHom.toRingHom.toAlgebra
  letI : IsLocalization.Away a Y.B := hloc
  apply CrysOver.Hom.ext p
  apply AlgHom.ext
  intro x
  change IsLocalization.Away.lift a (g := g.toAlgHom.toRingHom) hu (f.toAlgHom x) = g.toAlgHom x
  exact IsLocalization.Away.lift_eq a hu x

/-- 局所化からの厚化の射は、元の環からの合成で判定できる。 -/
theorem crysLocalization_hom_ext (f : X ⟶ Y) (a : X.B)
    (hloc : letI := f.toAlgHom.toRingHom.toAlgebra; IsLocalization.Away a Y.B)
    {g h : Y ⟶ Z} (hc : f ≫ g = f ≫ h) : g = h := by
  letI : Algebra X.B Y.B := f.toAlgHom.toRingHom.toAlgebra
  letI : IsLocalization.Away a Y.B := hloc
  have hco : g.toAlgHom.toRingHom.comp (algebraMap X.B Y.B) =
      h.toAlgHom.toRingHom.comp (algebraMap X.B Y.B) :=
    congrArg (fun t : X ⟶ Z => t.toAlgHom.toRingHom) hc
  have hh := IsLocalization.ringHom_ext (Submonoid.powers a) hco
  apply CrysOver.Hom.ext p
  apply AlgHom.ext
  intro y
  exact DFunLike.congr_fun hh y

end SerrePositivity.BhattScholze.Prismatic

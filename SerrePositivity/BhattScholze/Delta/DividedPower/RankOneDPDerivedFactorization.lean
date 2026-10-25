module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPTruncationDerived
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence
public import SerrePositivity.HomologicalAlgebra.FaithfullyFlatDerivedHomology

/-! # 一元分冪代数への実導来係数拡大の切断多項式環による因子化 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A]
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : P₀) ^ p)
local notation "G₀" => DividedPowerAlgebra A A
local notation "q₀" => AdjoinRoot.mk ((Polynomial.X : P₀) ^ p)

/-- 切断多項式環からの実分冪作用射は平坦な環射。 -/
theorem rankOneDPTruncatedRingHom_flat (hprime : p.Prime) (hp : (p : A) = 0) :
    (rankOneDPTruncatedMap hprime.pos hp).toRingHom.Flat := by
  let := rankOneDPTruncatedAlgebra hprime.pos hp
  exact rankOneDPTruncated_moduleFlat hprime hp

/-- 切断多項式環からの実分冪作用射は忠実平坦な環射。零環も含む。 -/
theorem rankOneDPTruncatedRingHom_faithfullyFlat (hprime : p.Prime) (hp : (p : A) = 0) :
    (rankOneDPTruncatedMap hprime.pos hp).toRingHom.FaithfullyFlat := by
  let := rankOneDPTruncatedAlgebra hprime.pos hp
  exact rankOneDPTruncated_moduleFaithfullyFlat hprime hp

/-- P→Γへの実導来係数拡大は、実射P→C→Γに沿う二段階の拡大と一致する。 -/
def rankOneDPDerivedFactorizationIso (hpos : 0 < p) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) :
    (boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X ≅
      (boundedAboveDerivedBaseChange (rankOneDPTruncatedMap hpos hp).toRingHom).obj
        ((boundedAboveDerivedBaseChange q₀).obj X) := by
  apply ObjectProperty.isoMk
  refine (boundedAboveDerivedBaseChangeModelIso _ X (boundedAboveDerivedChosenModel X)) ≪≫ ?_
  have hcomp := rankOneDPPolynomial_truncated_comp hpos hp
  rw [← hcomp]
  exact DerivedCategory.Q.mapIso (baseChangeCompIso q₀
      (rankOneDPTruncatedMap hpos hp).toRingHom (boundedAboveDerivedChosenModel X).complex).symm ≪≫
    (boundedAboveDerivedBaseChangeModelIso _ _ (boundedAboveDerivedBaseChangeModel q₀ X)).symm

/-- 素数標数では、P→Γの実導来拡大をCへの実導来拡大と通常の平坦拡大に分解できる。 -/
def rankOneDPDerivedFlatFactorizationIso (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) :
    ((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj ≅
      (flatDerivedBaseChange (rankOneDPTruncatedMap hprime.pos hp).toRingHom
        (rankOneDPTruncatedRingHom_flat hprime hp)).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj) :=
  DerivedCategory.Minus.ι.mapIso (rankOneDPDerivedFactorizationIso hprime.pos hp X) ≪≫
    (boundedAboveFlatDerivedBaseChangeIso (rankOneDPTruncatedMap hprime.pos hp).toRingHom
      (rankOneDPTruncatedRingHom_flat hprime hp)).app _

/-- 全次数の実ホモロジーは、切断多項式側の実ホモロジーの通常係数拡大で計算できる。 -/
def rankOneDPDerivedHomologyIso (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
      (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj) ≅
      (ModuleCat.extendScalars (rankOneDPTruncatedMap hprime.pos hp).toRingHom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
          (((boundedAboveDerivedBaseChange q₀).obj X).obj)) :=
  (DerivedCategory.homologyFunctor _ n).mapIso (rankOneDPDerivedFlatFactorizationIso hprime hp X) ≪≫
    (flatDerivedBaseChangeHomologyNatIso (rankOneDPTruncatedMap hprime.pos hp).toRingHom
      (rankOneDPTruncatedRingHom_flat hprime hp) n).app _

/-- 忠実平坦性により、分冪代数への実導来拡大は切断多項式側の各ホモロジーの零性を反映する。 -/
theorem rankOneDPDerivedHomology_isZero_iff (hprime : p.Prime) (hp : (p : A) = 0)
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
      (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj)) ↔
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
      (((boundedAboveDerivedBaseChange q₀).obj X).obj)) := by
  let Y := (((boundedAboveDerivedBaseChange q₀).obj X).obj)
  have h := faithfullyFlatDerivedHomology_map_eq_zero_iff
    (rankOneDPTruncatedMap hprime.pos hp).toRingHom
    (rankOneDPTruncatedRingHom_faithfullyFlat hprime hp) n
    (𝟙 Y)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id] at h
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
      ((flatDerivedBaseChange (rankOneDPTruncatedMap hprime.pos hp).toRingHom
        (rankOneDPTruncatedRingHom_flat hprime hp)).obj
          (((boundedAboveDerivedBaseChange q₀).obj X).obj))) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj)) := by
    simpa only [IsZero.iff_id_eq_zero] using h
  exact ((DerivedCategory.homologyFunctor _ n).mapIso
    (rankOneDPDerivedFlatFactorizationIso hprime hp X)).isZero_iff.trans hz

end SerrePositivity.BhattScholze

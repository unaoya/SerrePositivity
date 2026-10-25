module
public import SerrePositivity.InfinityCategories.Derived.KappaPerfect.Inclusion

/-!
概要：D 側の実加群比較から K-B 正本の DGKappaPerfectInput の三欄を構成する。
方針：全 Hom 比較同値の逆を取り、同じ包含の同型を余単位で移送する。
規約：DGKappaConeInput 自体は明示入力。D-8 c/d の存在や全高次作用は結論しない。
使われ方：D-8 e の供給入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 元の実 Perf から同じ cone 内の perfect 安定閉包への実関手。 -/
def dgKappaPerfectComparison : dgModulePerfectInfinityCategory R D ⟶
    dgStableClosureNerve R (DGKappaCone R D I) (dgKappaConePerfectObjects R D I) :=
  (dgKappaPerfectReverse_isQCatEquivalence R D I).choose.inv

/-- 比較は全写像空間の QCat 同値。 -/
theorem dgKappaPerfectComparison_isQCatEquivalence :
    IsQCatEquivalence (dgKappaPerfectComparison R D I) :=
  (dgKappaPerfectReverse_isQCatEquivalence R D I).choose.symm.isQCatEquivalence

/-- 同じ包含は β5 の元の Perf 包含と全関手で一致する。 -/
def dgKappaPerfectComparison_inclusionIso :
    FunctorIso
      ((dgKappaPerfectComparison R D I ≫ dgStableClosureInclusion R (DGKappaCone R D I)
        (dgKappaConePerfectObjects R D I)) ≫ dgKappaConeDerivedComparison R D I)
      (dgPerfectInclusionInfinity R D) := by
  have h := (FunctorIso.precomp (dgKappaPerfectReverse_inclusionIso R D I).symm
    (dgKappaPerfectComparison R D I)) ≪≫
      ((dgKappaPerfectReverse_isQCatEquivalence R D I).choose.invHomIso.postcomp
        (dgPerfectInclusionInfinity R D))
  simpa only [dgKappaPerfectComparison, Category.assoc] using! h

/-- D-8 e：正本の三欄を実関手・全写像空間同値・全関手同型で供給する。 -/
def dgKappaPerfectInput : DGKappaPerfectInput R D I where
  comparison := dgKappaPerfectComparison R D I
  isEquivalence := dgKappaPerfectComparison_isQCatEquivalence R D I
  inclusion := dgKappaPerfectComparison_inclusionIso R D I

end SerrePositivity.InfinityCategories

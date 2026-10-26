module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.SphereClosureConeInput
public import SerrePositivity.InfinityCategories.Derived.KappaPerfect.Input

/-!
概要：新しい sphere-only cone の、元の perfect 集合との全比較同値を供給する。
方針：telescope で再導出した perfectCovers を、既存の全 Hom 比較へ渡す。
規約：P の isEquivalence を弱めず、旧 cone／P の入口は変更しない。
使われ方：新模型の段提供者と、D-4b の実 Morita／P 比較。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

/-- D-2：新 cone の同じ perfect 集合との実比較同値。 -/
def dgKappaPerfectInput_unconditional' :
    DGKappaPerfectInput R D (dgKappaConeInput_unconditional' R D κ hκ) :=
  dgKappaPerfectInput R D (dgKappaConeInput_unconditional' R D κ hκ)

end SerrePositivity.InfinityCategories

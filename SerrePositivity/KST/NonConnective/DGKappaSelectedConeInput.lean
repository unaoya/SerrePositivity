module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.SphereClosureConeInput
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.SphereClosureInput
public import SerrePositivity.KST.NonConnective.DGKappaZeroFunctor

/-!
概要：K-7 が採用する無条件 cone・同じ P・実零所属の切替点を一つの葉へ集約する。
方針：現時点の D 正本を透過的に使い、段供給・再帰式・swindle はこの入口だけを参照する。
規約：D-2 の新正本を使う。I・P の型を変更しない。
使われ方：D-2 の新 cone 入力の到着時に、同じ固定 κ の実段供給を差し替える。
-/
@[expose] public noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)

/-- 採用実 cone の唯一の選択点。D-2 の sphere-only 正本を使う。 -/
def dgKappaSelectedConeInput : DGKappaConeInput R D κ :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgKappaConeInput_unconditional' R D κ hκ

/-- P は常に同じ採用 cone に対する D 正本の構成を使う。 -/
def dgKappaSelectedPerfectInput : DGKappaPerfectInput R D (dgKappaSelectedConeInput R D κ hκ) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaPerfect.dgKappaPerfectInput_unconditional' R D κ hκ

/-- 実零所属も採用模型に固定する。新模型の零所属供給はこの一箇所へ代入する。 -/
theorem dgKappaSelectedZeroInput : DGKappaZeroInput R D (dgKappaSelectedConeInput R D κ hκ) := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects R D κ (moduleZero R D)
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereClosureObjects_zero R D hκ

end SerrePositivity.KST.NonConnective

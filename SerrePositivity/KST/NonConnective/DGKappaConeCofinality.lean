module
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionCofinality
public import SerrePositivity.KST.NonConnective.DGKappaSplitCofiberSupply
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFEvaluationComparison
public import SerrePositivity.KST.SConstruction.KSpectrumConnectivity

/-!
概要：同じ cone の完備化後の K 零性を、共終性の仮定引数で完備化前へ戻す。
方針：元の実 Perf 評価比較で K 零性を戻し、正次数同型と零次単射を使う。
規約：同じ I・Z と共終性命題に条件付き。K₀ 全射性や cone 模型の存在は要求しない。
使われ方：K-7 c5・d3 の完備化前の連結 fibration の中央項の零性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ実 cone の元の Yoneda 始域を native 安定模型に保持する。
方針：I の前三角性を D 正本の宇宙移送後の安定性に渡す。
規約：同じ κ-compact dg 模型を選び直さない。
使われ方：完備化前の連結 fibration の中央 K 値。 -/
def dgKappaConeYonedaSource : StableModel.{max (u + 1) v} where
  carrier := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{max (u + 1) v, max (u + 1) v} (DGKappaCone R D I))
  stable := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftNerve_isStable R (DGKappaCone R D I)

/-- 概要：同じ実 cone の元の dg Yoneda を同じ実 Perf 値への完全射として保持する。
方針：D 正本の Yoneda 完全性を S• 保存条件へ移す。
規約：新たな対象・関手選択を加えない。
使われ方：同じ cone 上の共終性命題への実代入。 -/
def dgKappaConeYonedaStableMap : dgKappaConeYonedaSource R D I ⟶
    perfectDGStableModel R (DGKappaCone R D I) Set.univ := by
  let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity_isExactFunctor R (DGKappaCone R D I)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity R (DGKappaCone R D I),
    preservesCofiberData_of_isExactFunctor _⟩

/-- 概要：元の実 Perf 評価を介し、同じ cone の native Perf K の全整数群も自明。
方針：構成済みの同じ SOA K 零性を元の実評価 K 射の全単射性で移す。
規約：同じ I・Z に条件付きで、共終性供給はまだ使わない。
使われ方：完備化前の cone K 零性を回収するための標的。 -/
theorem dgKappaConeNativePerfectK_subsingleton (Z : DGKappaZeroInput R D I) (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (perfectDGStableModel R (DGKappaCone R D I) Set.univ)) j) := by
  letI : Subsingleton (OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (stableCategoryModel
        (presentedPerfectDGStableCategory R (dgKappaConeKInput R D I)))) j) := by
    simpa only [stableCategoryModel, presentedPerfectDGStableCategory,
      presentedPerfectDGQCat, presentedPerfectDGStableModel] using!
        dgKappaConnectedK_subsingleton_of_split R D I Z j
  have he := presentedPerfectDGBFEvaluationKMap_piIsomorphism R (dgKappaConeKInput R D I) j
  constructor
  intro x y
  obtain ⟨x', rfl⟩ := he.2 x
  obtain ⟨y', rfl⟩ := he.2 y
  exact congrArg (OmegaSpectrum.homotopyMap
    (presentedPerfectDGBFEvaluationKMap R (dgKappaConeKInput R D I)) j)
      (Subsingleton.elim x' y')

variable (hcofinal : ∀ (X Y : StableModel.{max (u + 1) v}) (f : X ⟶ Y),
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val →
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0))

include hcofinal in
/-- 概要：同じ cone の完備化前の native K の全整数群は、共終性供給に条件付きで自明。
方針：正次数の単射と零次の単射で元の Perf K 零性を反映し、負次数は連結性を使う。
規約：零次全射性も元の native cone の冪等完備性も仮定しない。
使われ方：完備化前の連結 fibration の同じ中央項を零にする。 -/
theorem dgKappaConeNativeK_subsingleton (Z : DGKappaZeroInput R D I) (j : ℤ) :
    Subsingleton (OmegaSpectrum.homotopyGroup
      (kOmegaSpectrum (dgKappaConeYonedaSource R D I)) j) := by
  let := dgKappaConeNativePerfectK_subsingleton R D I Z j
  have hc := hcofinal _ _ (dgKappaConeYonedaStableMap R D I)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPerfectYonedaInfinity_isIdempotentCompletion R (DGKappaCone R D I))
  by_cases hz : j = 0
  · subst j
    exact hc.2.subsingleton
  by_cases hp : 0 < j
  · exact (hc.1 j hp).1.subsingleton
  exact kOmegaSpectrum_negative_subsingleton _ j (by omega)

end SerrePositivity.KST.NonConnective

module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.FullSemifreeSubcategory
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.SupportModels
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.PerfectBasic

/-! # コホモロジーの台で切り出す導来 ∞ 部分圏

概要：閉集合 Z に台を持つ D_Z(S) と Perf_Z(S) を D(S) の全部分単体集合として定義する。
方針：各 semifree 複体の全ホモロジーに幾何学的な台条件を課す。
規約：一般には恒等射を消す一様な冪の存在とは区別する。使われ方：D9 の局所化の核。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (S : Type u) [CommRing S] (Z : TopologicalSpace.Closeds (PrimeSpectrum S))

/-- 概要：semifree 複体の全コホモロジーが Z に台を持つ条件。
方針：既存の幾何学的支持条件を使う。規約：非有界複体も許す。使われ方：D_Z の対象。 -/
def derivedSupportProperty (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) : Prop := HasHomologySupportOn Z P.val

/-- 概要：Z に台を持つ完全 semifree 複体の条件。
方針：完全モデル条件と幾何学的支持条件の両方を課す。
規約：同じ複体に対する条件。使われ方：Perf_Z の対象。 -/
def perfectSupportProperty (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) : Prop :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSemifreeProperty S P ∧ derivedSupportProperty S Z P

/-- 概要：D(S) の Z に台を持つ頂点が張る全部分単体集合。
方針：一般の対象条件による全部分構成を使う。
規約：D(S) の実際の Subcomplex。使われ方：D_Z の正本。 -/
def derivedSupportSubcomplex : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullSubcomplex S (derivedSupportProperty S Z)

/-- 概要：台つき導来 ∞ 圏 D_Z(S)。
方針：全部分単体集合の台を取る。規約：コホモロジーの台。使われ方：局所化の核。 -/
abbrev derivedSupportCategory : SSet.{u + 1} := derivedSupportSubcomplex S Z

/-- 概要：台つき完全対象で張られる全部分単体集合。
方針：二つの対象条件を同時に課す。規約：D(S) の Subcomplex。使われ方：Perf_Z の正本。 -/
def perfectSupportSubcomplex : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S).Subcomplex :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullSubcomplex S (perfectSupportProperty S Z)

/-- 概要：台つき完全導来 ∞ 圏 Perf_Z(S)。
方針：完全性と台の全部分単体集合を取る。規約：有限射影代表を許す。使われ方：K 理論 L4。 -/
abbrev perfectSupportCategory : SSet.{u + 1} := perfectSupportSubcomplex S Z

/-- 概要：Perf_Z は Perf と D_Z の実際の交わりである。
方針：全頂点における二条件を分配する。
規約：単体集合の部分複体としての等式。使われ方：Perf_Z の定義の展開。 -/
lemma perfectSupportSubcomplex_eq_inf :
    perfectSupportSubcomplex S Z = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectInfinitySubcomplex S ⊓ derivedSupportSubcomplex S Z := by
  ext n s
  exact forall_and

/-- 概要：D_Z は quasicategory である。
方針：全部分単体集合の一般構成を使う。規約：閉集合 Z は任意。使われ方：台つきホモトピー圏。 -/
instance derivedSupportCategory_quasicategory : SSet.Quasicategory (derivedSupportCategory S Z) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullSubcomplex_quasicategory S (derivedSupportProperty S Z)

/-- 概要：Perf_Z は quasicategory である。
方針：完全性と台の対象条件に全部分構成を適用する。
規約：有界性は有限射影代表にのみ課す。使われ方：K 理論の入力。 -/
instance perfectSupportCategory_quasicategory : SSet.Quasicategory (perfectSupportCategory S Z) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullSubcomplex_quasicategory S (perfectSupportProperty S Z)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

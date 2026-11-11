module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.SupportComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FullSemifreeCanonical
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality

/-! # 台つき有限射影代表と D5c の底変更の比較

概要：既存の perfect 圏で選ばれた代表の底変更は D5c の実際の頂点とホモトピー圏で同型である。
方針：共通像の比較同型に通常の係数変更関手を適用する。
規約：底変更は任意の環準同型でよい。使われ方：既存 K₀ の底変更との整合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (S : Type u) [CommRing S] (Z : TopologicalSpace.Closeds (PrimeSpectrum S))

/-- 概要：選ばれた有限射影代表の複体ホモトピー型は h Perf_Z の像と同型である。
方針：共通像への同値の余単位を包含関手で送る。
規約：既存の perfect 圏を使う。使われ方：底変更比較の基礎。 -/
def perfectSupportRepresentativeIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportHomotopyCategory S Z) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportClosedEquivalence S Z).functor.obj X).obj.obj ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportComplexHomotopyInclusion S Z).obj X :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.repletePerfectSupportProperty S Z).ι.mapIso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.strictPerfectSupportToReplete S Z).asEquivalence.counitIso.app
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportToReplete S Z).obj X))

/-- 概要：選ばれた有限射影代表は正本の頂点の複体とホモトピー同型である。
方針：標準単体包含と N3 の自然な比較同型を合成する。
規約：元の頂点の複体を終域とする。使われ方：D5c の頂点計算。 -/
def perfectSupportVertexRepresentativeIso (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportClosedEquivalence S Z).functor.obj ⟨x⟩).obj.obj ≅
      (HomotopyCategory.quotient _ _).obj (x.val.obj 0).val :=
  perfectSupportRepresentativeIso S Z ⟨x⟩ ≪≫
    (Functor.isoWhiskerRight
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeFullCanonicalH0Iso S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportProperty S Z))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S)).symm.app ⟨x⟩

variable {T : Type u} [CommRing T]

/-- 概要：既存の台つき係数変更と D5c の底変更は頂点のホモトピー型で一致する。
方針：有限射影代表の同型へ通常の係数変更を適用する。
規約：任意の環準同型、平坦性は不要。使われ方：K₀ の係数変更との比較。 -/
def perfectSupportBaseChangeIso (f : S →+* T) (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportCategory S Z) _⦋0⦌) :
    ((closedSupportChangeRing f Z (supportPullback f Z) le_rfl).obj
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.perfectSupportClosedEquivalence S Z).functor.obj ⟨x⟩)).obj.obj ≅
      (HomotopyCategory.quotient _ _).obj
        (((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f).app _ x.val).obj 0).val :=
  ((ModuleCat.extendScalars f).mapHomotopyCategory (.up ℤ)).mapIso
    (perfectSupportVertexRepresentativeIso S Z x)

end SerrePositivity.InfinityCategories.Project.DerivedCategories

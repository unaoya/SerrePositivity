module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingHomotopyGroups
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DerivedComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedPiZero
public import SerrePositivity.DifferentialGraded.Category.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Linear

/-! # 写像空間の π と導来 Ext

概要：semifree 複体の Hom コホモロジーを導来圏の整数次数 Ext と同定する。
方針：Mathlib の Hom コホモロジーのホモトピー射表示と K 射影性を使う。
規約：複体間の Ext^i は導来圏の Hom(X,Y[i])。使われ方：D10 の Ext の系。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S]

/-- 概要：任意 dg 圏の右写像空間の零次 π は Hom 複体の H⁰ と全単射である。
方針：N4 の π₀ と H⁰ の射の比較、および線形なホモロジー比較を合成する。
規約：π₀ は連結成分の集合。使われ方：正次数とは独立した零次数の比較。 -/
def pinchedHomPiZeroCohomologyEquiv {D : Type v} [DGCategory S D] (x y : D) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S D x y) ≃ (homObject S D x y).homology 0 :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.piZeroEquiv x y).trans
    (homotopyHomologyLinearEquiv S D (ForgetEnrichment.of (Complex S) x)
      (ForgetEnrichment.of (Complex S) y)).toEquiv

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：導来 ∞ 圏の頂点の整数次数 Ext を通常の導来圏で表す。
方針：対応する semifree 複体の導来像のシフトへの Hom を取る。
規約：整数 i に対する Ext^i(X,Y)=Hom_D(X,Y[i])。使われ方：π の Ext 表示の終域。 -/
abbrev derivedInfinityExt (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) (i : ℤ) :=
  ((DerivedCategory.Q : Complex S ⥤ DerivedCategory (ModuleCat.{u} S)).obj (x.obj 0).val ⟶
    ((DerivedCategory.Q : Complex S ⥤ DerivedCategory (ModuleCat.{u} S)).obj (y.obj 0).val)⟦i⟧)

/-- 概要：semifree 始域の Hom コホモロジーは整数次数の導来 Ext と加法群同型である。
方針：Hom コホモロジーをホモトピー射にし、K 射影の Qh 全単射とシフト比較を使う。
規約：終域は任意の非有界複体。使われ方：写像空間の Ext 計算。 -/
def semifreeHomCohomologyExtEquiv (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (Q : Complex S) (i : ℤ) :
    (homComplex S P.val Q).homology i ≃+
      ((DerivedCategory.Q : Complex S ⥤ DerivedCategory (ModuleCat.{u} S)).obj P.val ⟶
        ((DerivedCategory.Q : Complex S ⥤ DerivedCategory (ModuleCat.{u} S)).obj Q)⟦i⟧) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective S P.property
  let A := (HomotopyCategory.quotient _ _).obj P.val
  let B := (HomotopyCategory.quotient _ _).obj (Q⟦i⟧)
  let F := (DerivedCategory.Qh : _root_.HomotopyCategory (ModuleCat S) (.up ℤ) ⥤
    DerivedCategory (ModuleCat S))
  let eH : (A ⟶ B) ≃+ (F.obj A ⟶ F.obj B) :=
    AddEquiv.ofBijective F.mapAddHom (CochainComplex.IsKProjective.Qh_map_bijective P.val B)
  let eP := (DerivedCategory.quotientCompQhIso (ModuleCat S)).app P.val
  let eQ := (DerivedCategory.quotientCompQhIso (ModuleCat S)).app (Q⟦i⟧) ≪≫
    (DerivedCategory.Q.commShiftIso i).app Q
  exact ((CochainComplex.HomComplex.homologyLinearEquiv S P.val Q i).toAddEquiv.trans
    (CochainComplex.HomComplex.CohomologyClass.homAddEquiv
      (K := P.val) (L := Q) (n := i))).trans
      (eH.trans (Linear.homCongr S eP eQ).toAddEquiv)

/-- 概要：導来写像空間の π_{n+1} は Ext^{-n-1} と群同型である。
方針：正次数 π の Hom コホモロジー表示と K 射影 Ext 比較を合成する。
規約：零写像を基点とし、加法群は Multiplicative で表す。
使われ方：D10 の正次数の Ext の系。 -/
def derivedInfinityPiExtEquiv (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (x.obj 0) (y.obj 0)) n
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomZeroVertex (x.obj 0) (y.obj 0)) ≃*
        Multiplicative (derivedInfinityExt x y (-((n + 1 : ℕ) : ℤ))) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityPiCohomologyEquiv x y n).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.additiveGroupToMultiplicativeEquiv
      (semifreeHomCohomologyExtEquiv (x.obj 0) (y.obj 0).val (-((n + 1 : ℕ) : ℤ))))

/-- 概要：導来写像空間の π₀ は Ext⁰ と全単射である。
方針：N4 の零次比較と K 射影 Hom コホモロジー計算を使う。
規約：終域の零シフトを保持して Ext⁰ と表す。使われ方：D10 の零次数の系。 -/
def derivedInfinityPiZeroExtEquiv (x y : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S) (x.obj 0) (y.obj 0)) ≃ derivedInfinityExt x y 0 :=
  (pinchedHomPiZeroCohomologyEquiv (x.obj 0) (y.obj 0)).trans
    (semifreeHomCohomologyExtEquiv (x.obj 0) (y.obj 0).val 0).toEquiv

end SerrePositivity.InfinityCategories.Project.DerivedCategories

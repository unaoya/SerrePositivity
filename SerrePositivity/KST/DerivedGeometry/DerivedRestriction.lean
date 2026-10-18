module

public import SerrePositivity.KST.DerivedGeometry.OpenRestrictionExact

/-!
概要：完全な係数加群層の開制限を非有界導来圏へ降ろす。
方針：実際の完全関手の導来化と、コホモロジー比較を使う。
規約：係数の平坦性・複体の有界性は不要。
使われ方：TT 3.19・8.1、Toën §3.2 の局所化・降下の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory Limits AlgebraicGeometry
namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf
variable {X : Scheme.{u}} (B : CoefficientSheaf X) (U : X.Opens)

/--
概要：開制限した複体のコホモロジーはコホモロジー層の開制限。
方針：完全性による短複体のホモロジー比較を各次数で使う。
規約：実際の係数加群層のコホモロジーを比較する。
使われ方：TT 3.19・8.1 の台つき導来部分圏。
-/
def openRestrictionComplexHomologyIso (n : ℤ) :
    (B.openRestriction U).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor (B.restrict U).Modules (.up ℤ) n ≅
    HomologicalComplex.homologyFunctor B.Modules (.up ℤ) n ⋙ B.openRestriction U :=
  NatIso.ofComponents (fun K => (K.sc n).mapHomologyIso (B.openRestriction U))
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor B.Modules (.up ℤ) n).map f)
        (B.openRestriction U))

variable [HasDerivedCategory.{w} B.Modules] [HasDerivedCategory.{w'} (B.restrict U).Modules]

/--
概要：係数加群層の非有界導来圏の開制限。
方針：完全な層の開制限に Mathlib の導来化を適用する。
規約：局所化同値の存在を仮定しない。
使われ方：TT 3.19・8.1、Toën §3.2 の T2・T3。
-/
def derivedRestriction : DerivedCategory B.Modules ⥤ DerivedCategory (B.restrict U).Modules :=
  (B.openRestriction U).mapDerivedCategory

/--
概要：導来開制限は整数シフトと可換。
方針：完全関手の導来化の標準比較を保持する。
規約：Mathlib のシフト構造を使う。
使われ方：TT 3.19・8.1 の三角局所化。
-/
instance derivedRestriction_commShift : (B.derivedRestriction U).CommShift ℤ :=
  inferInstanceAs ((B.openRestriction U).mapDerivedCategory.CommShift ℤ)

/--
概要：導来開制限は三角関手。
方針：層の開制限の完全性を使う。
規約：非有界導来圏の標準三角構造。
使われ方：TT 3.19・8.1、Neeman 1992 Thm 2.1 の局所化。
-/
instance derivedRestriction_isTriangulated : (B.derivedRestriction U).IsTriangulated :=
  inferInstanceAs ((B.openRestriction U).mapDerivedCategory.IsTriangulated)

/--
概要：導来開制限のコホモロジーは元のコホモロジー層の開制限と自然同型。
方針：複体の比較を準同型局所化の前合成の全忠実性で降ろす。
規約：局所化で対象を選び直さず同じ関手の比較を与える。
使われ方：TT 3.19・8.1 の台つき対象と Dqc の制限。
-/
def derivedRestrictionHomologyIso (n : ℤ) :
    B.derivedRestriction U ⋙ DerivedCategory.homologyFunctor (B.restrict U).Modules n ≅
      DerivedCategory.homologyFunctor B.Modules n ⋙ B.openRestriction U := by
  apply (Localization.fullyFaithfulWhiskeringLeft (DerivedCategory.Q (C := B.Modules))
    (HomologicalComplex.quasiIso B.Modules (.up ℤ)) (B.restrict U).Modules).preimageIso
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (B.openRestriction U).mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors (B.restrict U).Modules n) ≪≫
    B.openRestrictionComplexHomologyIso U n ≪≫
    (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors B.Modules n) _).symm ≪≫
    Functor.associator _ _ _

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

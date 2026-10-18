module

public import SerrePositivity.KST.DerivedGeometry.CoefficientExact

/-!
# 係数加群層の導来忘却と準連接コホモロジー

概要：完全な係数忘却を導来化し、コホモロジーとの比較と保存性を証明する。
方針：複体のコホモロジーの比較を準同型による局所化へ降ろす。
規約：加群層の非有界導来圏を使い、各項の準連接性は要求しない。
使われ方：KST T1、Bondal–van den Bergh Thm 3.1.1 の係数版、Toën §3.2。
-/

@[expose] public section

noncomputable section

set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w w'

open CategoryTheory Limits AlgebraicGeometry

namespace SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

variable {X : Scheme.{u}} (B : CoefficientSheaf X)

/--
概要：複体の係数忘却はコホモロジーと可換。
方針：各次数の短複体に完全関手のコホモロジー比較を適用する。
規約：平坦性や有界性を仮定しない。
使われ方：KST T1、Toën §3.2 の導来忘却のコホモロジー比較。
-/
def forgetComplexHomologyIso (n : ℤ) :
    B.forget.mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.homologyFunctor X.Modules (.up ℤ) n ≅
    HomologicalComplex.homologyFunctor B.Modules (.up ℤ) n ⋙ B.forget :=
  NatIso.ofComponents
    (fun K => (K.sc n).mapHomologyIso B.forget)
    (fun f => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor B.Modules (.up ℤ) n).map f) B.forget)

variable [HasDerivedCategory.{w} B.Modules] [HasDerivedCategory.{w'} X.Modules]

/--
概要：係数加群層の非有界導来圏から構造層の導来圏への忘却。
方針：完全な層の忘却に Mathlib の導来化を適用する。
規約：自由・忘却随伴や生成定理は仮定しない。
使われ方：KST T1、Toën §3.2 の保存的な忘却関手。
-/
def derivedForget : DerivedCategory B.Modules ⥤ DerivedCategory X.Modules :=
  B.forget.mapDerivedCategory

/--
概要：導来忘却はシフトと可換。
方針：完全関手の導来化の標準比較を使う。
規約：シフトは整数添字。
使われ方：KST T1、Toën §3.2 の全シフトにわたる生成判定。
-/
instance derivedForget_commShift : B.derivedForget.CommShift ℤ :=
  inferInstanceAs (B.forget.mapDerivedCategory.CommShift ℤ)

/--
概要：導来忘却は三角関手。
方針：層の忘却の完全性から得た三角関手構造を使う。
規約：非有界導来圏の標準三角構造を使う。
使われ方：KST T1、Neeman 1992 Thm 2.1 の核の比較。
-/
instance derivedForget_isTriangulated : B.derivedForget.IsTriangulated :=
  inferInstanceAs (B.forget.mapDerivedCategory.IsTriangulated)

/--
概要：導来忘却のコホモロジーは係数コホモロジーを忘れた層に自然同型。
方針：複体の比較を局所化関手による前合成の全忠実性で降ろす。
規約：準同型による局所化の比較を明示する。
使われ方：KST T1、Toën §3.2 の保存性と D_qc の対象条件。
-/
def derivedForgetHomologyIso (n : ℤ) :
    B.derivedForget ⋙ DerivedCategory.homologyFunctor X.Modules n ≅
      B.underlyingCohomology n := by
  apply (Localization.fullyFaithfulWhiskeringLeft (DerivedCategory.Q (C := B.Modules))
    (HomologicalComplex.quasiIso B.Modules (.up ℤ)) X.Modules).preimageIso
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight B.forget.mapDerivedCategoryFactors _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (DerivedCategory.homologyFunctorFactors X.Modules n) ≪≫
    B.forgetComplexHomologyIso n ≪≫
    (Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors B.Modules n) _).symm ≪≫
    Functor.associator _ _ _

/--
概要：導来忘却は同型を反映する。
方針：全次数のコホモロジーで同型を判定し、層の忘却の同型反映性を使う。
規約：係数の平坦性を要求しない。
使われ方：KST T1、Bondal–van den Bergh Thm 3.1.1 の係数版の生成判定。
-/
instance derivedForget_reflectsIsomorphisms : B.derivedForget.ReflectsIsomorphisms where
  reflects {M N} f _ := by
    apply (DerivedCategory.isIso_iff B.Modules f).mpr
    intro n
    have h : IsIso ((B.underlyingCohomology n).map f) :=
      (NatIso.isIso_map_iff (B.derivedForgetHomologyIso n) f).mp
        (Functor.map_isIso (DerivedCategory.homologyFunctor X.Modules n) (B.derivedForget.map f))
    have : IsIso (B.forget.map ((DerivedCategory.homologyFunctor B.Modules n).map f)) := h
    exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor B.Modules n).map f) B.forget

end SerrePositivity.KST.DerivedGeometry.CoefficientSheaf

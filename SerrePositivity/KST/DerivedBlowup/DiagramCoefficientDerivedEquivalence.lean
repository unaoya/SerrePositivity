module

public import SerrePositivity.KST.DerivedBlowup.DiagramCoefficientQuasiEquivalence
public import SerrePositivity.DifferentialGraded.Functor.Closed
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の係数図式同型による全図式加群の導来比較。
方針：係数 dg 関手の opposite の準同値に既存の指定延長–制限同値を適用する。
規約：全図式加群の導来圏。cartesian・局所 perfect 部分圏への制限は別義務。
使われ方：例外因子の二つの係数表示の加群模型を比較する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable {F G : J ⥤ Mon (Complex R)}
variable [Small.{u} (DiagramModuleCoefficientObject F)]
variable [Small.{u} (DiagramModuleCoefficientObject G)]

/-- 概要：図式同型の係数 dg 関手に沿う指定導来制限。
方針：共変図式加群を係数圏の opposite 上の右加群として既存の制限を使う。
規約：KST §3.1。使われ方：導来表示比較の逆関手。 -/
abbrev diagramCoefficientDerivedRestriction (e : F ≅ G) :=
  dgDerivedRestriction R (DiagramModuleCoefficientObject F)ᵒᵖ
    (DiagramModuleCoefficientObject G)ᵒᵖ (diagramCoefficientDGFunctor e.hom).op

/-- 概要：係数図式同型による全図式加群の指定導来同値。
方針：構成済みの係数 dg 準同値を opposite へ移し、既存の導来 Morita 比較を使う。
規約：KST §3.1・Lemma 3.6、指定 graph 延長と制限を保つ。
使われ方：全図式の導来 mapping を保持した係数表示変更。 -/
def diagramCoefficientDerivedEquivalence (e : F ≅ G) :
    DerivedAllDiagramModules F ≌ DerivedAllDiagramModules G :=
  dgFunctorDerivedEquivalence R (DiagramModuleCoefficientObject F)ᵒᵖ
    (DiagramModuleCoefficientObject G)ᵒᵖ (diagramCoefficientDGFunctor e.hom).op
    (quasiEquivalence_op _ (diagramCoefficientDGFunctor_quasiEquivalence e))

/-- 概要：導来表示同値の順関手は元の指定 graph 導来延長。
方針：既存導来同値の定義を読む。
規約：KST Lemma 3.6。使われ方：局所係数拡大の指定比較との接続。 -/
theorem diagramCoefficientDerivedEquivalence_functor (e : F ≅ G) :
    (diagramCoefficientDerivedEquivalence e).functor =
      dgDerivedExtension R (DiagramModuleCoefficientObject F)ᵒᵖ
        (DiagramModuleCoefficientObject G)ᵒᵖ (diagramCoefficientDGFunctor e.hom).op := rfl

/-- 概要：導来表示同値の逆関手は元の指定導来制限。
方針：既存延長–制限同値の定義を読む。
規約：KST Lemma 3.6。使われ方：対象条件を局所評価の指定制限で比較する。 -/
theorem diagramCoefficientDerivedEquivalence_inverse (e : F ≅ G) :
    (diagramCoefficientDerivedEquivalence e).inverse = diagramCoefficientDerivedRestriction e := rfl

end SerrePositivity.KST.DerivedBlowup

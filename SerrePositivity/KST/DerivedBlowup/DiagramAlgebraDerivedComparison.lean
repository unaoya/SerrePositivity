module

public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedEvaluation
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction

/-!
概要：KST §3.1 の一対象正規表示における canonical な導来局所比較。
方針：指定加群比較を標準計算同型で主局所化へ移し、導来延長–制限随伴で送る。
規約：全 diagram-module の主導来圏と指定の単位矢の経路を保持する。
使われ方：正規表示での cartesian 条件と導来比較の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：正規表示の局所 dg 遷移に沿う導来制限。
方針：構成済みの局所 dg 関手の opposite に一般の導来制限を適用する。
規約：KST §3.1。使われ方：指定制限比較の行先。 -/
abbrev diagramAlgebraDerivedRestriction {i j : J} (h : i ≤ j) :=
  dgDerivedRestriction R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (diagramAlgebraVertexTransition F h).op

/-- 概要：正規表示の局所 dg 遷移に沿う実際の導来係数拡大。
方針：graph tensor の射影的分解を用いる構成済み導来延長を適用する。
規約：KST §3.1。使われ方：cartesian 比較の始域。 -/
abbrev diagramAlgebraDerivedExtension {i j : J} (h : i ≤ j) :=
  dgDerivedExtension R (AlgebraVertex (F.obj i))ᵒᵖ (AlgebraVertex (F.obj j))ᵒᵖ
    (diagramAlgebraVertexTransition F h).op

/-- 概要：目標の導来評価を局所制限した関手の標準計算同型。
方針：評価と局所制限の二つの因子分解同型を合成する。
規約：KST §3.1。使われ方：指定加群比較の導来化で行先を同定する。 -/
def diagramAlgebraDerivedRestrictedEvaluationIso {i j : J} (h : i ≤ j) :
    moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ ⋙
        diagramAlgebraDerivedEvaluation F j ⋙ diagramAlgebraDerivedRestriction F h ≅
      diagramAlgebraIteratedEvaluation F h ⋙ moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ :=
  isoWhiskerRight (diagramAlgebraDerivedEvaluationIso F j) (diagramAlgebraDerivedRestriction F h) ≪≫
    isoWhiskerLeft (diagramAlgebraModuleEvaluation F j)
      (eqToIso (dgDerivedRestriction_fac R (AlgebraVertex (F.obj i))ᵒᵖ
        (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op))

/-- 概要：主局所化前の加群上の指定導来制限比較の自然変換。
方針：標準評価同型、指定加群比較の局所化、標準制限計算同型の逆を合成する。
規約：KST §3.1。使われ方：主局所化への自然変換の延長の入力。 -/
def diagramAlgebraDerivedRestrictionPreNatTrans {i j : J} (h : i ≤ j) :
    moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ ⋙
        diagramAlgebraDerivedEvaluation F i ⟶
      moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ ⋙
        diagramAlgebraDerivedEvaluation F j ⋙ diagramAlgebraDerivedRestriction F h :=
  (diagramAlgebraDerivedEvaluationIso F i).hom ≫
    whiskerRight (diagramAlgebraModuleComparisonNatTrans F h)
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ) ≫
    (diagramAlgebraDerivedRestrictedEvaluationIso F h).inv

/-- 概要：全図式の主導来局所化上の指定局所制限比較の自然変換。
方針：主局所化の構成済み自然変換延長を適用する。
規約：KST §3.1。使われ方：canonical な係数拡大比較の随伴前の射。 -/
def diagramAlgebraDerivedRestrictionNatTrans {i j : J} (h : i ≤ j) :
    diagramAlgebraDerivedEvaluation F i ⟶
      diagramAlgebraDerivedEvaluation F j ⋙ diagramAlgebraDerivedRestriction F h :=
  Localization.Construction.natTransExtension
    (W := moduleQuasiIso R (DiagramModuleCoefficientObject F)ᵒᵖ)
    (diagramAlgebraDerivedRestrictionPreNatTrans F h)

/-- 概要：正規表示の canonical な導来係数拡大比較射。
方針：指定制限比較の成分を実際の導来延長–制限随伴の逆で送る。
規約：KST §3.1、任意同型の存在や選択を仮定しない。
使われ方：指定射の可逆性による cartesian 条件。 -/
def diagramAlgebraDerivedExtensionComparison {i j : J} (h : i ≤ j)
    (X : DerivedAllDiagramModules F) :
    (diagramAlgebraDerivedExtension F h).obj ((diagramAlgebraDerivedEvaluation F i).obj X) ⟶
      (diagramAlgebraDerivedEvaluation F j).obj X :=
  ((dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
    (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op).homEquiv _ _).symm
      ((diagramAlgebraDerivedRestrictionNatTrans F h).app X)

/-- 概要：指定導来係数拡大比較の随伴像は元の指定制限比較。
方針：構成済み Hom 同値の逆元律を使う。
規約：KST §3.1。使われ方：指定した比較の計算経路の確認。 -/
theorem diagramAlgebraDerivedExtensionComparison_adjunct {i j : J} (h : i ≤ j)
    (X : DerivedAllDiagramModules F) :
    (dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
      (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op).homEquiv _ _
        (diagramAlgebraDerivedExtensionComparison F h X) =
      (diagramAlgebraDerivedRestrictionNatTrans F h).app X :=
  Equiv.apply_symm_apply _ _

set_option maxHeartbeats 2000000 in
-- 指定 graph 随伴の Hom 同値と複数の導来評価の型を照合するために必要。
/-- 概要：正規表示の指定係数拡大比較は全導来図式加群の射について自然。
方針：随伴 Hom 同値の単射性と自然性で指定制限比較の自然性へ戻す。
規約：KST §3.1。使われ方：cartesian 条件の同型不変性。 -/
theorem diagramAlgebraDerivedExtensionComparison_natural {i j : J} (h : i ≤ j)
    {X Y : DerivedAllDiagramModules F} (f : X ⟶ Y) :
    (diagramAlgebraDerivedExtension F h).map ((diagramAlgebraDerivedEvaluation F i).map f) ≫
        diagramAlgebraDerivedExtensionComparison F h Y =
      diagramAlgebraDerivedExtensionComparison F h X ≫
        (diagramAlgebraDerivedEvaluation F j).map f := by
  let A := dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
    (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op
  apply (A.homEquiv _ _).injective
  rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right,
    diagramAlgebraDerivedExtensionComparison_adjunct,
    diagramAlgebraDerivedExtensionComparison_adjunct]
  exact (diagramAlgebraDerivedRestrictionNatTrans F h).naturality f

/-- 概要：正規表示の導来係数拡大比較の自然変換。
方針：構成した指定射と証明済みの自然性を束ねる。
規約：KST §3.1。使われ方：大域 Perf 候補の cartesian 比較。 -/
def diagramAlgebraDerivedExtensionNatTrans {i j : J} (h : i ≤ j) :
    diagramAlgebraDerivedEvaluation F i ⋙ diagramAlgebraDerivedExtension F h ⟶
      diagramAlgebraDerivedEvaluation F j where
  app X := diagramAlgebraDerivedExtensionComparison F h X
  naturality _ _ f := diagramAlgebraDerivedExtensionComparison_natural F h f

end SerrePositivity.KST.DerivedBlowup

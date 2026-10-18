module

public import SerrePositivity.KST.DerivedBlowup.DiagramStructureRegularTransition
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComputation
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionComputation
public import SerrePositivity.KST.DerivedBlowup.RepresentableDerivedExtensionComparison

/-!
概要：KST §3.1 の構造加群の直接 regular 比較と指定導来遷移の整合性。
方針：加群段階の指定可換式を主局所化へ送り、指定延長–制限随伴で移す。
規約：標準分解に沿う代表延長比較を使い、随伴像の一致を確認する。
使われ方：構造加群の canonical な cartesian 比較の可逆性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite
open DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：直接 Yoneda 射から作る構造加群の指定局所 regular 導来同型。
方針：直接比較の擬同型性を主局所化で反転する。
規約：KST §3.1。使われ方：指定係数拡大比較を通す局所同型。 -/
def diagramStructureRegularDerivedIso (i : J) :
    (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).obj
      (ForgetEnrichment.of (Complex R) (representable R (op (.point : AlgebraVertex (F.obj i))))) ≅
      (diagramAlgebraDerivedEvaluation F i).obj (derivedDiagramStructureModule F) :=
  moduleDerivedIso R (AlgebraVertex (F.obj i))ᵒᵖ (diagramStructureLocalRegularMap F i)
    (diagramStructureLocalRegularMap_quasiIso F i)

/-- 概要：指定局所 regular 導来同型の順射は直接 Yoneda 比較の局所化像。
方針：指定擬同型を反転する構成の順射を計算する。
規約：KST §3.1。使われ方：加群段階の可換式の導来化。 -/
theorem diagramStructureRegularDerivedIso_hom (i : J) :
    (diagramStructureRegularDerivedIso F i).hom =
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        (diagramStructureLocalRegularMap F i) := rfl

set_option maxHeartbeats 2000000 in
-- 二つの局所導来同型と指定導来制限比較の型を照合するために必要。
/-- 概要：構造加群の指定導来制限比較は局所 regular 同型を介して代表制限比較と一致する。
方針：各射を実加群の主局所化像に戻し、構成済み加群段階の可換式を送る。
規約：KST §3.1。使われ方：指定係数拡大比較の随伴像の一致。 -/
theorem diagramStructureRegularDerivedIso_restriction {i j : J} (h : i ≤ j) :
    (diagramStructureRegularDerivedIso F i).hom ≫
        (diagramAlgebraDerivedRestrictionNatTrans F h).app (derivedDiagramStructureModule F) =
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
          (representableRestrictionMap R (AlgebraVertex (F.obj i))ᵒᵖ
            (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op (op .point)) ≫
        (diagramAlgebraDerivedRestriction F h).map (diagramStructureRegularDerivedIso F j).hom := by
  rw [diagramStructureRegularDerivedIso_hom, diagramStructureRegularDerivedIso_hom]
  change (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
      (diagramStructureLocalRegularMap F i) ≫
      (diagramAlgebraDerivedRestrictionNatTrans F h).app
        ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj
          (diagramStructureModule F)) = _
  rw [diagramAlgebraDerivedRestrictionNatTrans_app_Q_map, transitionDerivedRestriction_map_Q]
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map)
      (diagramStructureLocalRegularMap_transition F h)

set_option maxHeartbeats 2000000 in
-- 指定 graph 随伴の自然性と局所 regular 同型を照合するために必要。
/-- 概要：構造加群の指定係数拡大比較は局所 regular 同型を介して代表延長比較と一致する。
方針：指定随伴の Hom 同値で比較し、制限側の可換式と代表延長比較の随伴公式を使う。
規約：KST §3.1。使われ方：canonical な cartesian 比較の可逆性を導く。 -/
theorem diagramStructureRegularDerivedIso_extension {i j : J} (h : i ≤ j) :
    (diagramAlgebraDerivedExtension F h).map (diagramStructureRegularDerivedIso F i).hom ≫
        diagramAlgebraDerivedExtensionComparison F h (derivedDiagramStructureModule F) =
      canonicalRepresentableDerivedExtensionMap R (AlgebraVertex (F.obj i))ᵒᵖ
          (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op (op .point) ≫
        (diagramStructureRegularDerivedIso F j).hom := by
  let A := dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
    (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op
  apply (A.homEquiv _ _).injective
  rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right]
  rw [diagramAlgebraDerivedExtensionComparison_adjunct,
    canonicalRepresentableDerivedExtensionMap_adjunct]
  exact diagramStructureRegularDerivedIso_restriction F h

end SerrePositivity.KST.DerivedBlowup

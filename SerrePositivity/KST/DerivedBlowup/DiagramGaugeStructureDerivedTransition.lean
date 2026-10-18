module

public import SerrePositivity.KST.DerivedBlowup.DiagramGaugeStructureRegularTransition
public import SerrePositivity.KST.DerivedBlowup.DiagramAlgebraDerivedComputation
public import SerrePositivity.KST.DerivedBlowup.TransitionDerivedRestrictionComputation
public import SerrePositivity.KST.DerivedBlowup.RepresentableDerivedExtensionComparison

/-!
概要：KST §3.1 の捻りの直接 regular 比較と指定導来遷移の可換式。
方針：加群段階の可換式を主局所化へ送り、指定延長–制限随伴で移す。
規約：代表延長比較・重み自己同型・直接比較の指定経路を保持する。
使われ方：O(m) の canonical な係数拡大比較の可逆性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory Opposite DifferentialGraded

variable {R : Type u} [CommRing R] {J : Type v} [Preorder J] [DecidableLE J]
variable (F : J ⥤ Mon (Complex R)) (s : DiagramHomGauge F)
variable [Small.{u} (DiagramModuleCoefficientObject F)]

/-- 概要：指定 gauge で捻った構造加群の主導来対象。
方針：実際の全図式加群を指定局所化へ送る。
規約：KST §3.1。使われ方：具体的 O(m) の一般形。 -/
abbrev derivedDiagramGaugeStructureModule : DerivedAllDiagramModules F :=
  (moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj
    (diagramGaugeStructureModule F s)

/-- 概要：直接 Yoneda 射を順射に持つ指定局所 regular 導来同型。
方針：通常加群圏での可逆性を指定主局所化へ送る。
規約：KST §3.1。使われ方：canonical な係数拡大比較を通す局所同型。 -/
def diagramGaugeStructureRegularDerivedIso (i : J) :
    (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).obj
      (ForgetEnrichment.of (Complex R) (representable R (op (.point : AlgebraVertex (F.obj i))))) ≅
      (diagramAlgebraDerivedEvaluation F i).obj (derivedDiagramGaugeStructureModule F s) := by
  letI := diagramGaugeStructureLocalRegularMap_isIso F s i
  exact (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).mapIso
    (asIso (diagramGaugeStructureLocalRegularMap F s i))

/-- 概要：指定 regular 導来同型の順射は直接 Yoneda 比較の主局所化像。
方針：指定射の同型を送る構成の順射を読む。
規約：KST §3.1。使われ方：加群段階の可換式を導来化する。 -/
theorem diagramGaugeStructureRegularDerivedIso_hom (i : J) :
    (diagramGaugeStructureRegularDerivedIso F s i).hom =
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
        (diagramGaugeStructureLocalRegularMap F s i) := rfl

/-- 概要：包含の重み自己同型と直接比較の合成を主導来圏へ送った局所同型。
方針：通常加群圏での二つの同型を合成して指定局所化へ送る。
規約：KST §3.1。使われ方：指定遷移の行先の可逆な重み付き比較。 -/
def diagramGaugeStructureWeightedDerivedIso {i j : J} (h : i ≤ j) :
    (moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).obj
      (ForgetEnrichment.of (Complex R) (representable R (op (.point : AlgebraVertex (F.obj j))))) ≅
      (diagramAlgebraDerivedEvaluation F j).obj (derivedDiagramGaugeStructureModule F s) := by
  letI := diagramGaugeStructureLocalRegularMap_isIso F s j
  exact (moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).mapIso
    (diagramGaugeRegularIso F s h ≪≫ asIso (diagramGaugeStructureLocalRegularMap F s j))

/-- 概要：重み付き局所導来同型の順射は二つの指定加群射の合成の像。
方針：指定主局所化における同型の順射を計算する。
規約：KST §3.1。使われ方：加群遷移の可換式をそのまま導来化する。 -/
theorem diagramGaugeStructureWeightedDerivedIso_hom {i j : J} (h : i ≤ j) :
    (diagramGaugeStructureWeightedDerivedIso F s h).hom =
      (moduleToDerived R (AlgebraVertex (F.obj j))ᵒᵖ).map
        ((diagramGaugeRegularIso F s h).hom ≫ diagramGaugeStructureLocalRegularMap F s j) := rfl

set_option maxHeartbeats 2000000 in
-- 指定局所導来比較と実加群の局所化像の型を照合するために必要。
/-- 概要：指定導来制限比較は regular 同型を介して代表制限比較と重み付き同型に一致。
方針：指定各射を実加群の主局所化像へ戻し、加群段階の可換式を送る。
規約：KST §3.1。使われ方：canonical な係数拡大比較の随伴像の一致。 -/
theorem diagramGaugeStructureRegularDerivedIso_restriction {i j : J} (h : i ≤ j) :
    (diagramGaugeStructureRegularDerivedIso F s i).hom ≫
        (diagramAlgebraDerivedRestrictionNatTrans F h).app
          (derivedDiagramGaugeStructureModule F s) =
      (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
          (representableRestrictionMap R (AlgebraVertex (F.obj i))ᵒᵖ
            (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op (op .point)) ≫
        (diagramAlgebraDerivedRestriction F h).map
          (diagramGaugeStructureWeightedDerivedIso F s h).hom := by
  rw [diagramGaugeStructureRegularDerivedIso_hom, diagramGaugeStructureWeightedDerivedIso_hom]
  change (moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map
      (diagramGaugeStructureLocalRegularMap F s i) ≫
      (diagramAlgebraDerivedRestrictionNatTrans F h).app
        ((moduleToDerived R (DiagramModuleCoefficientObject F)ᵒᵖ).obj
          (diagramGaugeStructureModule F s)) = _
  rw [diagramAlgebraDerivedRestrictionNatTrans_app_Q_map, transitionDerivedRestriction_map_Q]
  simpa only [CategoryTheory.Functor.map_comp] using
    congrArg ((moduleToDerived R (AlgebraVertex (F.obj i))ᵒᵖ).map)
      (diagramGaugeStructureLocalRegularMap_transition F s h)

set_option maxHeartbeats 2000000 in
-- 指定随伴の自然性と局所 regular 同型の型を照合するために必要。
/-- 概要：指定係数拡大比較は代表延長比較と重み付き局所同型の合成に一致。
方針：指定随伴の Hom 同値で比較し、制限側の可換式と代表延長の随伴式を使う。
規約：KST §3.1。使われ方：canonical な捻り比較の可逆性。 -/
theorem diagramGaugeStructureRegularDerivedIso_extension {i j : J} (h : i ≤ j) :
    (diagramAlgebraDerivedExtension F h).map (diagramGaugeStructureRegularDerivedIso F s i).hom ≫
        diagramAlgebraDerivedExtensionComparison F h (derivedDiagramGaugeStructureModule F s) =
      canonicalRepresentableDerivedExtensionMap R (AlgebraVertex (F.obj i))ᵒᵖ
          (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op (op .point) ≫
        (diagramGaugeStructureWeightedDerivedIso F s h).hom := by
  let A := dgDerivedExtensionRestrictionAdjunction R (AlgebraVertex (F.obj i))ᵒᵖ
    (AlgebraVertex (F.obj j))ᵒᵖ (diagramAlgebraVertexTransition F h).op
  apply (A.homEquiv _ _).injective
  rw [A.homEquiv_naturality_left, A.homEquiv_naturality_right]
  rw [diagramAlgebraDerivedExtensionComparison_adjunct,
    canonicalRepresentableDerivedExtensionMap_adjunct]
  exact diagramGaugeStructureRegularDerivedIso_restriction F s h

end SerrePositivity.KST.DerivedBlowup

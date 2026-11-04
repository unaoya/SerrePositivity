module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldCocartesianPostBaseChange
public import SerrePositivity.KST.Fibration.ScaffoldCocartesianBaseChange
public import SerrePositivity.KST.Fibration.StrictTransportPostEvaluation
public import SerrePositivity.KST.Fibration.LeftCocartesianClassificationPoint

/-! # 同じ strict Kan 後合成の係数点を、元の実 fiber 写像と底変換を通して分類する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {I : Type u} [Category.{u} I] {E T B : SSet.{u}} [Quasicategory B]
  (s : T ⟶ nerve I) (p : E ⟶ B) [LeftFibration p] (k : nerve I ⟶ B)
  (f : T ⟶ pullback p k) (hf : f ≫ pullback.snd p k = s)

omit [Quasicategory B] in
/-- 同じ Kan 自然変換の単位上の実点は、元の strict section の後合成の単位像。 -/
theorem strictKanTransportPost_unit_point (c : I)
    (v : ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram s).obj c) _⦋0⦌) :
    (((strictKanTransportPostToLeftFibration s (pullback.snd p k) f hf).app c).app
      (Opposite.op ⦋0⦌))
        ((F2.continuousKanReplacementUnit.app
          ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram s).obj c)).app (Opposite.op ⦋0⦌) v) =
    (F2.continuousKanReplacementUnit.app
      ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram (pullback.snd p k)).obj c)).app
        (Opposite.op ⦋0⦌)
        (((strictTransportPostToLeftFibration s (pullback.snd p k) f hf).app c).app
          (Opposite.op ⦋0⦌) v) :=
  (congrArg (fun m => m.app (Opposite.op ⦋0⦌) v)
    (F2.continuousKanReplacementUnit.naturality
      ((strictTransportPostToLeftFibration s (pullback.snd p k) f hf).app c))).symm

omit [Quasicategory B] in
/-- 後合成した同じ section の strict 評価は、元の section 評価の実 fiber 写像による像。 -/
theorem strictTransportPost_inclusion_evaluate (c : I)
    (v : ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram s).obj c) _⦋0⦌) :
    (leftStrictTransportEvaluate (pullback.snd p k) c).app (Opposite.op ⦋0⦌)
      (((cocartesianStrictTransportInclusion (pullback.snd p k)).app c).app
        (Opposite.op ⦋0⦌)
        (((strictTransportPostToLeftFibration s (pullback.snd p k) f hf).app c).app
          (Opposite.op ⦋0⦌) v)) =
    (vertexFiberMap s (pullback.snd p k) f hf (nerveVertex c)).app (Opposite.op ⦋0⦌)
      ((SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate s c).app (Opposite.op ⦋0⦌) v) := by
  have hi := congrArg (fun m => m.app (Opposite.op ⦋0⦌)
    (((strictTransportPostToLeftFibration s (pullback.snd p k) f hf).app c).app
      (Opposite.op ⦋0⦌) v)) (leftCocartesianStrictTransportEvaluation_eq (pullback.snd p k) c)
  have he := congrArg (fun m => m.app (Opposite.op ⦋0⦌) v)
    (strictTransportPostToLeftFibration_evaluate s (pullback.snd p k) f hf c)
  exact hi.trans he

/-- 元の全 Kan 後合成と分類比較の実点作用は、同じ評価・fiber 写像・第一射影を保持する。 -/
theorem scaffoldCocartesianPostBaseChangeClassification_pointHom (c : I)
    (v : ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram s).obj c) _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((cocartesianKanDiagram (pullback.snd p k)).obj c)).symm
      ((((strictKanTransportPostToLeftFibration s (pullback.snd p k) f hf).app c).app
        (Opposite.op ⦋0⦌))
          ((F2.continuousKanReplacementUnit.app
            ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram s).obj c)).app (Opposite.op ⦋0⦌) v))) ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (kanDiagramCoherentNerve_vertex (cocartesianKanDiagram (pullback.snd p k)) c))).inv ≫
      functorHomEvaluate (scaffoldCocartesianBaseChangeClassificationIso p k).hom
        (ULift.up (nerveVertex c)) =
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint p
      (k.app (Opposite.op ⦋0⦌) (nerveVertex c))
      ((cofinalVertexFiberBaseChangeIso p k (nerveVertex c)).hom.app (Opposite.op ⦋0⦌)
        ((vertexFiberMap s (pullback.snd p k) f hf (nerveVertex c)).app (Opposite.op ⦋0⦌)
          ((SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate s c).app (Opposite.op ⦋0⦌) v)))) := by
  rw [strictKanTransportPost_unit_point s p k f hf c v]
  have h := scaffoldCocartesianBaseChangeClassificationIso_pointHom p k c
    (((strictTransportPostToLeftFibration s (pullback.snd p k) f hf).app c).app
      (Opposite.op ⦋0⦌) v)
  exact h.trans (congrArg (fun w => cosliceFiberPointHom (scaffoldReconstructionFiberPoint p
    (k.app (Opposite.op ⦋0⦌) (nerveVertex c))
    ((cofinalVertexFiberBaseChangeIso p k (nerveVertex c)).hom.app (Opposite.op ⦋0⦌) w)))
      (strictTransportPost_inclusion_evaluate s p k f hf c v))

end SerrePositivity.KST.Fibration

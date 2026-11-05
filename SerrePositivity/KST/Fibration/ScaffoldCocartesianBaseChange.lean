module
public import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldCocartesianBaseChange
import SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldCocartesianBaseChange
public import SerrePositivity.KST.Fibration.ScaffoldCocartesianClassification
public import SerrePositivity.KST.Fibration.ScaffoldVertexBaseChange

/-! # 元の cocartesian 切断の分類と、実底変換の指定点を同じ scaffold 復元で比較する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

variable {I : Type u} [Category.{u} I] {E B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [LeftFibration p] (k : nerve I ⟶ B)

/-- 同じ cocartesian 切断の Kan 分類を、元の底の実図式へ同じ底変換成分で送る。 -/
def scaffoldCocartesianBaseChangeClassificationIso :
    FunctorIso (cocartesianKanCoherentDiagram (pullback.snd p k))
      ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningInfinityDiagram p) :=
  scaffoldCocartesianKanClassificationIso (pullback.snd p k) ≪≫
    (leftStraighteningInfinityDiagram_baseChangeIso p k).symm

/-- 元の section 包含・恒等射評価・実 fiber 底変換の同じ点を保持する分類比較。 -/
theorem scaffoldCocartesianBaseChangeClassificationIso_pointHom (c : I)
    (v : ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram (pullback.snd p k)).obj c) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((cocartesianKanDiagram (pullback.snd p k)).obj c)).symm
        ((F2.continuousKanReplacementUnit.app
          ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram (pullback.snd p k)).obj c)).app
            (Opposite.op ⦋0⦌) v)) ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (kanDiagramCoherentNerve_vertex (cocartesianKanDiagram (pullback.snd p k)) c))).inv ≫
      functorHomEvaluate (scaffoldCocartesianBaseChangeClassificationIso p k).hom
        (ULift.up (nerveVertex c)) =
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint p
      (k.app (Opposite.op ⦋0⦌) (nerveVertex c))
      ((cofinalVertexFiberBaseChangeIso p k (nerveVertex c)).hom.app (Opposite.op ⦋0⦌)
        ((leftStrictTransportEvaluate (pullback.snd p k) c).app (Opposite.op ⦋0⦌)
          (((cocartesianStrictTransportInclusion (pullback.snd p k)).app c).app
            (Opposite.op ⦋0⦌) v)))) := by
  let z := ULift.up.{u + 1} (nerveVertex c)
  let w := (leftStrictTransportEvaluate (pullback.snd p k) c).app (Opposite.op ⦋0⦌)
    (((cocartesianStrictTransportInclusion (pullback.snd p k)).app c).app (Opposite.op ⦋0⦌) v)
  let e := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue (leftStraighteningInfinityDiagram_baseChangeIso p k) z
  have hc := scaffoldCocartesianKanClassificationIso_pointHom (pullback.snd p k) c v
  have hb := scaffoldPointedReconstruction_baseChange_pointHom p k (nerveVertex c) w
  have hi := _root_.SerrePositivity.InfinityCategories.Stable.Transport.recoverPoint e _ _ hb
  have hinv := _root_.SerrePositivity.InfinityCategories.F1.Transport.functorIsoValue_inv (leftStraighteningInfinityDiagram_baseChangeIso p k) z
  rw [hinv] at hi
  have hs := _root_.SerrePositivity.InfinityCategories.Stable.Transport.appendPoint _ _ _ _
    (functorHomEvaluate (leftStraighteningInfinityDiagram_baseChangeIso p k).inv z) hc
  have he := hs.trans hi
  change _ ≫ _ ≫ functorHomEvaluate
    ((scaffoldCocartesianKanClassificationIso (pullback.snd p k)).hom ≫
      (leftStraighteningInfinityDiagram_baseChangeIso p k).inv) z = _
  rw [functorHomEvaluate_comp]
  exact he

end SerrePositivity.KST.Fibration

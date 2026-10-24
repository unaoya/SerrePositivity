module
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

private lemma recoverPoint {C : Type*} [Category C] {a b z : C}
    (e : a ≅ b) (x : z ⟶ a) (y : z ⟶ b) (h : x ≫ e.hom = y) :
    y ≫ e.inv = x := by
  rw [← h]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private lemma appendPoint {C : Type*} [Category C] {a b c d e : C}
    (x : a ⟶ b) (y : b ⟶ c) (f : c ⟶ d) (z : a ⟶ d) (g : d ⟶ e)
    (h : x ≫ y ≫ f = z) : x ≫ y ≫ f ≫ g = z ≫ g := by
  simpa only [Category.assoc] using congrArg (fun m => m ≫ g) h

variable {I : Type u} [Category.{u} I] {E B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [LeftFibration p] (k : nerve I ⟶ B)

local instance : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 同じ cocartesian 切断の Kan 分類を、元の底の実図式へ同じ底変換成分で送る。 -/
def scaffoldCocartesianBaseChangeClassificationIso :
    FunctorIso (cocartesianKanCoherentDiagram (pullback.snd p k))
      ((SSet.uliftFunctor.{u + 1, u}).map k ≫ leftStraighteningInfinityDiagram p) :=
  scaffoldCocartesianKanClassificationIso (pullback.snd p k) ≪≫
    (leftStraighteningInfinityDiagram_baseChangeIso p k).symm

/-- 元の section 包含・恒等射評価・実 fiber 底変換の同じ点を保持する分類比較。 -/
theorem scaffoldCocartesianBaseChangeClassificationIso_pointHom (c : I)
    (v : ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram (pullback.snd p k)).obj c) _⦋0⦌) :
    cosliceFiberPointHom ((pointedSpaceFiberVertexEquiv
      ((cocartesianKanDiagram (pullback.snd p k)).obj c)).symm
        ((F2.continuousKanReplacementUnit.app
          ((SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram (pullback.snd p k)).obj c)).app
            (Opposite.op ⦋0⦌) v)) ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (kanDiagramCoherentNerve_vertex (cocartesianKanDiagram (pullback.snd p k)) c))).inv ≫
      functorHomEvaluate (scaffoldCocartesianBaseChangeClassificationIso p k).hom
        (ULift.up (nerveVertex c)) =
    cosliceFiberPointHom (scaffoldReconstructionFiberPoint p
      (k.app (Opposite.op ⦋0⦌) (nerveVertex c))
      ((cofinalVertexFiberBaseChangeIso p k (nerveVertex c)).hom.app (Opposite.op ⦋0⦌)
        ((leftStrictTransportEvaluate (pullback.snd p k) c).app (Opposite.op ⦋0⦌)
          (((cocartesianStrictTransportInclusion (pullback.snd p k)).app c).app
            (Opposite.op ⦋0⦌) v)))) := by
  let z := ULift.up.{u + 1} (nerveVertex c)
  let w := (leftStrictTransportEvaluate (pullback.snd p k) c).app (Opposite.op ⦋0⦌)
    (((cocartesianStrictTransportInclusion (pullback.snd p k)).app c).app (Opposite.op ⦋0⦌) v)
  let e := functorIsoValue (leftStraighteningInfinityDiagram_baseChangeIso p k) z
  have hc := scaffoldCocartesianKanClassificationIso_pointHom (pullback.snd p k) c v
  have hb := scaffoldPointedReconstruction_baseChange_pointHom p k (nerveVertex c) w
  have hi := recoverPoint e _ _ hb
  have hinv := functorIsoValue_inv (leftStraighteningInfinityDiagram_baseChangeIso p k) z
  rw [hinv] at hi
  have hs := appendPoint _ _ _ _
    (functorHomEvaluate (leftStraighteningInfinityDiagram_baseChangeIso p k).inv z) hc
  have he := hs.trans hi
  change _ ≫ _ ≫ functorHomEvaluate
    ((scaffoldCocartesianKanClassificationIso (pullback.snd p k)).hom ≫
      (leftStraighteningInfinityDiagram_baseChangeIso p k).inv) z = _
  rw [functorHomEvaluate_comp]
  exact he

end SerrePositivity.KST.Fibration

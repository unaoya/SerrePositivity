module

public import SerrePositivity.KST.LocalizingInvariants.TammeSpanDenominatorBaseChange
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.VertexFiberNervePullback

/-!
概要：任意の底図式上の span 族の実 fiber を元の両端固定 span と同定する。
方針：固定第一終点の fiber 同型と底変換の fiber 同型を合成する。
規約：全単体上の実同型。使われ方：分母上の両端 fiber の亜群化を元の分数模型へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

def tammeSpanDiagramFiberIso (x : (laxCategory p q).obj _⦋0⦌)
    {B : SSet.{u}} (f : B ⟶ (laxCategory p q).obj) (b : B _⦋0⦌) :
    fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x
        (f.app (Opposite.op ⦋0⦌) b) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x) f) b :=
  markedSpanFamilyFiberIso _ _ _ _ ≪≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso _ _ _).symm

lemma tammeSpanDiagramFiberIso_hom_inclusion (x : (laxCategory p q).obj _⦋0⦌)
    {B : SSet.{u}} (f : B ⟶ (laxCategory p q).obj) (b : B _⦋0⦌) :
    (tammeSpanDiagramFiberIso p q x f b).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x) f) b ≫
      pullback.fst
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x) f =
      (markedSpanFamilyFiberIso (laxCategory p q).obj (tammeLocalizingEdges p q) x
        (f.app (Opposite.op ⦋0⦌) b)).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x)
          (f.app (Opposite.op ⦋0⦌) b) := by
  dsimp only [tammeSpanDiagramFiberIso, Iso.trans_hom, Iso.symm_hom]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso_hom_ι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.KST.LocalizingInvariants

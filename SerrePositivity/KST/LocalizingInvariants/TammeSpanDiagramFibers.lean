module

public import SerrePositivity.KST.LocalizingInvariants.TammeSpanDenominatorBaseChange
public import SerrePositivity.InfinityCategories.Core.VertexFiberNervePullback

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
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

def tammeSpanDiagramFiberIso (x : (laxCategory p q).obj _⦋0⦌)
    {B : SSet.{u}} (f : B ⟶ (laxCategory p q).obj) (b : B _⦋0⦌) :
    fixedMarkedSpans (laxCategory p q).obj (tammeLocalizingEdges p q) x
        (f.app (Opposite.op ⦋0⦌) b) ≅
      vertexFiber (pullback.snd
        (markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x) f) b :=
  markedSpanFamilyFiberIso _ _ _ _ ≪≫ (SerrePositivity.InfinityCategories.vertexFiberPullbackIso _ _ _).symm

lemma tammeSpanDiagramFiberIso_hom_inclusion (x : (laxCategory p q).obj _⦋0⦌)
    {B : SSet.{u}} (f : B ⟶ (laxCategory p q).obj) (b : B _⦋0⦌) :
    (tammeSpanDiagramFiberIso p q x f b).hom ≫
      vertexFiberι (pullback.snd
        (markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x) f) b ≫
      pullback.fst
        (markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x) f =
      (markedSpanFamilyFiberIso (laxCategory p q).obj (tammeLocalizingEdges p q) x
        (f.app (Opposite.op ⦋0⦌) b)).hom ≫
        vertexFiberι
          (markedSpanFamilyProjection (laxCategory p q).obj (tammeLocalizingEdges p q) x)
          (f.app (Opposite.op ⦋0⦌) b) := by
  dsimp only [tammeSpanDiagramFiberIso, Iso.trans_hom, Iso.symm_hom]
  rw [← SerrePositivity.InfinityCategories.vertexFiberPullbackIso_hom_ι]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

end SerrePositivity.KST.LocalizingInvariants

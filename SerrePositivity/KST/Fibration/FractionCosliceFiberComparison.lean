module
public import SerrePositivity.KST.Fibration.FractionCosliceBaseChange
public import SerrePositivity.InfinityCategories.Core.VertexFiberMap
public import SerrePositivity.InfinityCategories.F1.PullbackTransport
public import SerrePositivity.InfinityCategories.F1B.KanScaffoldPullbackFiber

/-! # 元の底上の全分数比較と、同じ固定分数評価との厳密な fiber 比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {X Q T : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : InvertsEdges F W) (x : X _⦋0⦌) (k : T ⟶ X) (b : T _⦋0⦌)

/-- 同じ底図式への引き戻しと両端固定分数空間との、元の厳密な fiber 同型。 -/
def fractionSourceFiberIso :
    fixedMarkedSpans X W x (k.app (Opposite.op ⦋0⦌) b) ≅
      vertexFiber (pullback.snd (markedSpanFamilyProjection X W x) k) b :=
  markedSpanFamilyFiberIso _ _ _ _ ≪≫ (KanSection.vertexFiberPullbackIso _ _ _).symm

/-- 同じ全分数比較が各 fiber に誘導する元の実写像。 -/
def fractionCosliceFiberMap :
    vertexFiber (pullback.snd (markedSpanFamilyProjection X W x) k) b ⟶
      vertexFiber (pullback.snd
        (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x))) (k ≫ F)) b :=
  vertexFiberMap _ _ (fractionCosliceBaseChange F W hF x k)
    (fractionCosliceBaseChange_snd F W hF x k) b

omit [Quasicategory Q] in
/-- 元の固定分数から引き戻しへ移しても、第一射影は同じ固定第一終点族を回収する。 -/
theorem fractionSourceFiberIso_ambient : (fractionSourceFiberIso W x k b).hom ≫
    vertexFiberι (pullback.snd (markedSpanFamilyProjection X W x) k) b ≫
      pullback.fst (markedSpanFamilyProjection X W x) k =
        fixedMarkedSpanToFamily X W x (k.app (Opposite.op ⦋0⦌) b) := by
  rw [fractionSourceFiberIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ← KanSection.vertexFiberPullbackIso_hom_ι,
    ← Category.assoc (KanSection.vertexFiberPullbackIso _ _ _).inv,
    Iso.inv_hom_id, Category.id_comp]
  rfl

/-- 元の同じ fiber 同型で戻すと、全比較は既存の固定分数 coslice 評価そのもの。 -/
theorem fractionCosliceFiberMap_fixed :
    (fractionSourceFiberIso W x k b).hom ≫ fractionCosliceFiberMap F W hF x k b ≫
      (vertexFiberPullbackIso
        (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
        (k ≫ F) b).hom =
      fixedFractionCosliceEvaluation F W hF x (k.app (Opposite.op ⦋0⦌) b) := by
  apply vertexFiber_hom_ext
    (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
    (F.app (Opposite.op ⦋0⦌) (k.app (Opposite.op ⦋0⦌) b))
  have ht : (vertexFiberPullbackIso
      (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
      (k ≫ F) b).hom ≫ vertexFiberι
        (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
        (F.app (Opposite.op ⦋0⦌) (k.app (Opposite.op ⦋0⦌) b)) =
      vertexFiberι (pullback.snd
        (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x))) (k ≫ F)) b ≫
        pullback.fst _ (k ≫ F) := vertexFiberPullbackIso_hom_ι _ _ _
  rw [Category.assoc, Category.assoc, ht,
    ← Category.assoc (fractionCosliceFiberMap F W hF x k b), fractionCosliceFiberMap,
    vertexFiberMap_ι, Category.assoc, fractionCosliceBaseChange_fst,
    fixedFractionCosliceEvaluation_inclusion]
  simpa only [Category.assoc] using congrArg
    (fun m => m ≫ fractionFamilyCosliceEvaluation F W hF x)
    (fractionSourceFiberIso_ambient W x k b)

/-- 逆の fiber 同型を用いると、元の比較の順方向の射そのものを既存の評価で表示できる。 -/
theorem fractionCosliceFiberMap_unfixed :
    fractionCosliceFiberMap F W hF x k b ≫
      (vertexFiberPullbackIso
        (sliceUnderProjection (yonedaEquiv.symm (F.app (Opposite.op ⦋0⦌) x)))
        (k ≫ F) b).hom =
      (fractionSourceFiberIso W x k b).inv ≫
        fixedFractionCosliceEvaluation F W hF x (k.app (Opposite.op ⦋0⦌) b) := by
  have he := congrArg (fun m => (fractionSourceFiberIso W x k b).inv ≫ m)
    (fractionCosliceFiberMap_fixed F W hF x k b)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using he

end SerrePositivity.KST.Fibration

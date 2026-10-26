module
public import SerrePositivity.KST.SConstruction.Cofinality.CokernelSimplicialSet

/-!
概要：元の指定射の余核図式から同じ余核群の nerve への単体的写像。
方針：全区間値の関手を各単体に割り当て、全端点制限で自然性を確認する。
規約：面・退化の一部だけで比較を定義しない。
使われ方：障害図式の bar 同型の元の順射。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の余核図式を区間値により群 nerve へ写す。
方針：任意の単体作用素の下で区間制限の合成を照合する。
規約：同じ指定射の S₁ 余核の群を使う。
使われ方：離散的障害の単体的な bar 比較。 -/
def cutCokernelNerveMap {X Y : StableModel.{u}} (f : X ⟶ Y) :
    cutCokernelSimplicialSet f ⟶
      nerve (AsSmall.{u} (SingleObj (Multiplicative (cutKZeroCokernel 1 f)))) where
  app n := ↾(cutCokernelNerveSimplex f n.unop.len)
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro a
    change cutKZeroCokernel d.unop.len f at a
    change cutCokernelNerveSimplex f e.unop.len (cutCokernelRestriction f α.unop.toOrderHom a) =
      (cutCokernelNerveSimplex f d.unop.len a).whiskerLeft
        (SimplexCategory.toCat.map α.unop).toFunctor
    refine CategoryTheory.Functor.hext
      (F := cutCokernelNerveSimplex f e.unop.len (cutCokernelRestriction f α.unop.toOrderHom a))
      (G := (cutCokernelNerveSimplex f d.unop.len a).whiskerLeft
        (SimplexCategory.toCat.map α.unop).toFunctor) (fun _ => rfl) ?_
    intro i j β
    apply heq_of_eq
    apply ULift.ext
    change Multiplicative.ofAdd
        (cutCokernelRestriction f (cokernelIntervalOrder _ _ _) (cutCokernelRestriction f
          α.unop.toOrderHom a)) =
      Multiplicative.ofAdd (cutCokernelRestriction f (cokernelIntervalOrder _ _ _) a)
    apply congrArg Multiplicative.ofAdd
    exact (DFunLike.congr_fun (cutCokernelRestriction_comp f
      (cokernelIntervalOrder _ _ _) α.unop.toOrderHom) a).symm.trans
        (DFunLike.congr_fun (congrArg (cutCokernelRestriction f)
          (cokernelIntervalOrder_comp α.unop.toOrderHom _ _ _)) a)

end SerrePositivity.KST.SConstruction.Cofinality

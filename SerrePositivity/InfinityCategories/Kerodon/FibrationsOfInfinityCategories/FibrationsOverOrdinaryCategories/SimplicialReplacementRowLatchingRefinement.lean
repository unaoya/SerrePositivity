module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementRowEpiLifts

/-!
概要：同じ非退化表示から、元の任意のlatching表示への射と係数の持ち上げを作る。
方針：基底の全射表示の共通因子をOverの射にし、同じ係数を始点の等式で戻す。
規約：基底だけでなく元の係数の単体も実際のlatching作用素で回収する。
使われ方：IS-W2 R03f.2の任意の余錐に対する表示の独立性。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open CategoryTheory Limits SSet
open SerrePositivity.Reedy
open scoped Simplicial
variable {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u}) {n m : ℕ}

/-- 同じ全射の合成の等式を、元のlatchingの射そのものにする。 -/
def simplicialReplacementLatchingRefinement (hm : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α]
    (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌)) (γ : j.obj.left.unop ⟶ ⦋m⦌)
    (h : j.obj.hom.unop ≫ γ = α) : simplicialReplacementLatchingIndexOfEpi hm α ⟶ j :=
  ObjectProperty.homMk (Over.homMk γ.op (by
    change γ.op ≫ j.obj.hom = α.op
    simpa only [op_comp, Quiver.Hom.op_unop] using congrArg Quiver.Hom.op h))

/-- 元の任意のlatching表示は、同じ非退化表示から係数も含めて回収される。 -/
theorem simplicialReplacementRowLatching_refine (q : SimplexCategoryᵒᵖ)
    (hm : m < n) (α : ⦋n⦌ ⟶ ⦋m⦌) [Epi α] (τ : (nerve I).nonDegenerate m)
    (j : LatchingIndex simplexOp (Opposite.op ⦋n⦌))
    (x : ((simplicialReplacementRows F).obj j.obj.left).obj q)
    (h : (nerve I).map α.op τ =
      (((simplicialReplacementRows F).map j.obj.hom).app q x).1) :
    ∃ (f : simplicialReplacementLatchingIndexOfEpi hm α ⟶ j)
      (y : (F.obj (τ.val.obj 0)).obj q),
      ((simplicialReplacementRows F).map f.hom.left).app q ⟨τ.val,y⟩ = x := by
  haveI : Epi j.obj.hom.unop := j.property.1
  change (nerve I).map α.op τ = (nerve I).map j.obj.hom.unop.op x.1 at h
  obtain ⟨γ, hγ, hc, ht⟩ := simplicialReplacement_common_nondegenerate_presentation
    α τ j.obj.hom.unop x.1 h
  haveI : Epi γ := hγ
  obtain ⟨y, hy⟩ := simplicialReplacementRowReindex_lift F γ τ.val q x ht
  exact ⟨simplicialReplacementLatchingRefinement hm α j γ hc, y, hy⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

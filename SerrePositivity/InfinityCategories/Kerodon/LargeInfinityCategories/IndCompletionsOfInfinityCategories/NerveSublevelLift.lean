module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

public import Mathlib.CategoryTheory.Limits.Preorder

/-!
概要：全頂点が一つの添字以下なら、同じ nerve 図式はその下区間に因子分解する。
方針：各鎖の頂点を元の図式の自然性で比較し、下区間の部分型へ持ち上げる。
規約：元の全単体の値を保つ。単に頂点の関数を作るだけで済ませない。
使われ方：共通上界を厳密な頂点とする添字の余錐。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Preorder I] {K : SSet.{u}}

/-- 同じ下区間の包含関手。 -/
def sublevelInclusion (i : I) : Set.Iic i ⥤ I where
  obj x := x.val
  map h := homOfLE (leOfHom h)

/-- 全頂点の上界を使い、元の全鎖を同じ下区間へ持ち上げる。 -/
def nerveSublevelLift (a : K ⟶ nerve I) (i : I)
    (ha : ∀ v : K _⦋0⦌, (a.app _ v).obj 0 ≤ i) : K ⟶ nerve (Set.Iic i) where
  app n := ↾fun s =>
    { obj j := ⟨(a.app n s).obj j, by
        have hh := ha (K.map (SimplexCategory.const ⦋0⦌ n.unop j).op s)
        have hn := ConcreteCategory.congr_hom
          (a.naturality (SimplexCategory.const ⦋0⦌ n.unop j).op) s
        change a.app _ (K.map (SimplexCategory.const ⦋0⦌ n.unop j).op s) =
          (nerve I).map (SimplexCategory.const ⦋0⦌ n.unop j).op (a.app n s) at hn
        rw [hn] at hh
        exact hh⟩
      map h := homOfLE (leOfHom ((a.app n s).map h)) }
  naturality {n m} β := by
    apply ConcreteCategory.hom_ext
    intro s
    refine CategoryTheory.Functor.ext (fun j => ?_) (fun _ _ _ => Subsingleton.elim _ _)
    apply Subtype.ext
    have hn := ConcreteCategory.congr_hom (a.naturality β) s
    change a.app m (K.map β s) = (nerve I).map β (a.app n s) at hn
    exact congrArg (fun q => q.obj j) hn

/-- 下区間の包含と合成すると元の同じ図式に厳密に戻る。 -/
lemma nerveSublevelLift_inclusion (a : K ⟶ nerve I) (i : I)
    (ha : ∀ v : K _⦋0⦌, (a.app _ v).obj 0 ≤ i) :
    nerveSublevelLift a i ha ≫ nerveMap (sublevelInclusion i) = a := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change ((nerveSublevelLift a i ha).app n s) ⋙ sublevelInclusion i = a.app n s
  exact CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

module
public import SerrePositivity.KST.SConstruction.CubeDeletionNormalUsed

/-! # 削除・max の二段表示の一意性
概要：元の全頂点写像から残余入力次元と削除因子、全 max ブロックを回収する。
方針：一座標頂点が検出する使用入力と、削除写像の全射性を使う。
規約：中間次元は任意。使われ方：全混合語の三段表示の一意性。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の全頂点関数は、二段表示全体を一意に決める。 -/
lemma cubeDeletionConnectionNormalVertex_injective (n m : ℕ) :
    Function.Injective (cubeDeletionConnectionNormalVertex (n := n) (m := m)) := by
  intro r s h
  have hu := cubeDeletionConnectionNormal_used_eq_of_vertex_eq r s h
  rcases r with ⟨a, d, c⟩
  rcases s with ⟨b, e, f⟩
  have hab : a = b := cubeDeletionNormal_dimension_of_used d e hu
  subst b
  have hde : d = e := cubeDeletionNormal_eq_of_used d e hu
  subst e
  have hcf : c = f := by
    apply cubeConnectionNormalVertex_injective
    funext y
    obtain ⟨x, hx⟩ := cubeDeletionNormalVertex_surjective d y
    have hxy := congrFun h x
    change cubeConnectionNormalVertex c (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d x) =
      cubeConnectionNormalVertex f (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d x) at hxy
    rw [hx] at hxy
    exact hxy
  subst f
  rfl

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.CubeDeletionConnectionDetection

/-! # 三段標準表示の具体的な頂点写像による一意性
概要：元の頂点写像は二つの中間次元と、削除・max・面の全因子を一意に決める。
方針：端点から面を回収し、面の単射性で二段接頭部へ帰着する。
規約：表示の中間次元は仮定でそろえない。使われ方：語の Serre 評価の意味による降下。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 三段表示の零頂点は、元の面の零頂点を回収する。 -/
lemma cubeThreeNormalVertex_bot {n m : ℕ} (r : CubeThreeNormal n m) :
    cubeThreeNormalVertex r ⊥ = cubeFaceNormalVertex r.face ⊥ := by
  dsimp only [cubeThreeNormalVertex, Function.comp_apply]
  rw [cubeDeletionNormalVertex_bot, cubeConnectionNormalVertex_bot]

/-- 三段表示の一頂点は、元の面の一頂点を回収する。 -/
lemma cubeThreeNormalVertex_top {n m : ℕ} (r : CubeThreeNormal n m) :
    cubeThreeNormalVertex r ⊤ = cubeFaceNormalVertex r.face ⊤ := by
  dsimp only [cubeThreeNormalVertex, Function.comp_apply]
  rw [cubeDeletionNormalVertex_top, cubeConnectionNormalVertex_top]

/-- 元の全頂点写像は、削除・max・面の三段表示を一意に決める。 -/
lemma cubeThreeNormalVertex_injective (n m : ℕ) :
    Function.Injective (cubeThreeNormalVertex (n := n) (m := m)) := by
  intro r s h
  have hz : cubeFaceNormalVertex r.face ⊥ = cubeFaceNormalVertex s.face ⊥ := by
    rw [← cubeThreeNormalVertex_bot, ← cubeThreeNormalVertex_bot, h]
  have ho : cubeFaceNormalVertex r.face ⊤ = cubeFaceNormalVertex s.face ⊤ := by
    rw [← cubeThreeNormalVertex_top, ← cubeThreeNormalVertex_top, h]
  rcases r with ⟨a, b, d, c, f⟩
  rcases s with ⟨a', b', d', c', f'⟩
  have hbb : b = b' := cubeFaceNormal_dimension_of_endpoints f f' hz ho
  subst b'
  have hff : f = f' := cubeFaceNormal_eq_of_endpoints f f' hz ho
  subst f'
  have hp : cubeDeletionConnectionNormalVertex (⟨a, d, c⟩ :
      CubeDeletionConnectionNormal n b) = cubeDeletionConnectionNormalVertex ⟨a', d', c'⟩ := by
    funext x
    apply cubeFaceNormalVertex_injective_input f
    exact congrFun h x
  have he := cubeDeletionConnectionNormalVertex_injective n b hp
  cases he
  rfl

end SerrePositivity.KST.SConstruction

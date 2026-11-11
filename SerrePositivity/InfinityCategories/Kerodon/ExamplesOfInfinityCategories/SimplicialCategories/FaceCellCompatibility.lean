module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FaceHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HornCells

/-!
# 共通単体上での面の Hom 候補の一致

概要：ホーンの二つの面から作った Hom 候補を同じ単体上で比較する。
方針：faceRetraction、factor_δ、SimplicialNerve の関手性により共通単体の回収へ戻す。
規約：共通単体への全ての制限に対して厳密な等式を証明する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の重なり。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section

universe v u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

variable {C : Type u} [Category.{v} C] [SimplicialCategory C]
set_option backward.isDefEq.respectTransparency false in
/-- 概要：任意の既知面を避ける単体上で、面の Hom 候補は共通単体の Hom 回収に等しい。
方針：退化と θ の合成が factor_δ となることを nerve の自然性へ移し、型の移送を消去する。
規約：θ の単射性や局所 Kan 性は不要。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の面どうしの重なり。 -/
lemma hornHomViaFace_on_cell {m n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (θ : ⦋m⦌ ⟶ ⦋n + 2⦌) (j : Fin (n + 3)) (hj : j ≠ i)
    (hθ : ∀ k, θ.toOrderHom k ≠ j) (a b : Fin (m + 1)) :
    (SimplicialThickening.functor θ.toOrderHom.uliftMap).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj (θ.toOrderHom a) (θ.toOrderHom b) (hθ a) (hθ b) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornCellHom σ θ j hj hθ a b := by
  apply eq_of_heq
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornCellHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomOnCell, ← Category.assoc,
    comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  let F := σ.app _ (SSet.horn.face i j hj)
  have hF : (SimplicialNerve C).map θ.op
      ((SimplicialNerve C).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction j).op F) =
        σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornCell i θ j hj hθ) := by
    rw [← CategoryTheory.Functor.map_comp_apply, ← op_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.faceRetraction_factor]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornRestriction_from_face i σ θ j hj hθ).symm
  have hmap (F G : EnrichedFunctor SSet
      (SimplicialThickening (ULift.{v} (Fin (m + 1)))) C) (h : F = G) :
      HEq (F.map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) (G.map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩) := by
    subst G
    rfl
  exact hmap _ _ hF

/-- 概要：二つの除外頂点を避ける単体上で両方の面の Hom 候補は厳密に一致する。
方針：両者を同じ単体の Hom 回収へ戻す。
規約：両面が元のホーンに含まれることを仮定する。
使われ方：HTT 1.1.5.10、Kerodon 2.4.5.8（Tag 00LR） の零座標面の貼合せの共通部分。 -/
lemma hornHomViaFace_common_cell {m n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ SimplicialNerve C)
    (θ : ⦋m⦌ ⟶ ⦋n + 2⦌) (j k : Fin (n + 3)) (hj : j ≠ i) (hk : k ≠ i)
    (hθj : ∀ a, θ.toOrderHom a ≠ j) (hθk : ∀ a, θ.toOrderHom a ≠ k)
    (a b : Fin (m + 1)) :
    (SimplicialThickening.functor θ.toOrderHom.uliftMap).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ j hj (θ.toOrderHom a) (θ.toOrderHom b) (hθj a) (hθj b) =
    (SimplicialThickening.functor θ.toOrderHom.uliftMap).map ⟨⟨a⟩⟩ ⟨⟨b⟩⟩ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornHomViaFace σ k hk (θ.toOrderHom a) (θ.toOrderHom b) (hθk a) (hθk b) := by
  rw [hornHomViaFace_on_cell, hornHomViaFace_on_cell, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.hornCellHom_independent]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

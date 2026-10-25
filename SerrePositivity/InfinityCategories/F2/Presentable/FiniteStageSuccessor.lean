module

public import SerrePositivity.InfinityCategories.F2.Presentable.FiniteStageSourceCoslice
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import SerrePositivity.InfinityCategories.Core.SimplexVertexDetection

/-!
概要：元の小さい有限表示前置図式の後続段と宇宙持ち上げを比較する。
方針：coslice の宇宙同型を全余錐値へ展開する。
規約：元の小さい添字を維持し、後続頂点を取り替えない。
使われ方：全交互有限段と元の filtered 表示の再帰的な整合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：有限前置 coslice の宇宙比較は元の全余錐の持ち上げの制限。
方針：一般の coslice 同型の値と標準単体の逆同型を展開する。
規約：全余錐の厳密な等式。
使われ方：後続表示段の全高次成分の回収。 -/
lemma finiteStageSourceCosliceIso_val {n : ℕ} {I : SSet.{u}}
    (a : (Δ[n] : SSet.{u}) ⟶ I) (j : (sliceUnder a) _⦋0⦌) :
    ((finiteStageSourceCosliceIso a).hom.app (Opposite.op ⦋0⦌) (ULift.up j)).val =
      joinMap (uliftStdSimplexIso.{u, u + 1} n).inv (𝟙 Δ[0]) ≫
        (JoinCocone.ulift.{u, u + 1} j).val := by
  change joinMap (uliftStdSimplexIso.{u, u + 1} n).inv (𝟙 Δ[0]) ≫
    ((uliftSliceUnderIso a).hom.app (Opposite.op ⦋0⦌) (ULift.up j)).val = _
  rw [uliftSliceUnderIso_hom_val]
  rfl

/-- 概要：元の小さい後続余錐を次の標準単体の表示前置図式にする。
方針：標準単体と点の join の同型で表示する。
規約：元の後続余錐の全射を使う。
使われ方：小さい添字内の有限再帰。 -/
def finiteStageSuccessor {n : ℕ} {I : SSet.{u}}
    {a : (Δ[n] : SSet.{u}) ⟶ I} (j : (sliceUnder a) _⦋0⦌) :
    (Δ[n + 1] : SSet.{u}) ⟶ I :=
  (joinStdSimplexIso n 0).inv ≫ j.val

/-- 概要：後続段を join 表示へ戻すと元の小さい余錐全体になる。
方針：標準単体同型の相殺。
規約：全射の等式。
使われ方：次の有限前置図式の固定条件。 -/
lemma finiteStageSuccessor_join {n : ℕ} {I : SSet.{u}}
    {a : (Δ[n] : SSet.{u}) ⟶ I} (j : (sliceUnder a) _⦋0⦌) :
    (joinStdSimplexIso n 0).hom ≫ finiteStageSuccessor j = j.val := by
  simp [finiteStageSuccessor]

private lemma finiteJoinUniverse_naturality (n : ℕ) :
    (SSet.uliftFunctor.{u + 1, u}).map (joinStdSimplexIso n 0).hom ≫
        (uliftStdSimplexIso.{u, u + 1} (n + 1)).hom =
      (uliftCoconeShapeIso.{u, u + 1} (Δ[n] : SSet.{u}) 0).hom ≫
        joinMap (uliftStdSimplexIso.{u, u + 1} n).hom (𝟙 Δ[0]) ≫
          (joinStdSimplexIso n 0).hom := by
  apply stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨i, x, y⟩⟩
  fin_cases i
  · cases x
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    rfl
  · cases y
    apply SSet.stdSimplex.obj₀Equiv.injective
    apply Fin.ext
    rfl

/-- 概要：後続の大きい標準表示は、元の小さい全余錐の宇宙比較と一致する。
方針：標準 join 同型の宇宙自然性と同型の相殺を使う。
規約：任意の標的 I への全射を比較する。
使われ方：偶数前置図式を元の小さい filtered 添字に保つ。 -/
lemma finiteStageSuccessor_base_join {n : ℕ} {I : SSet.{u}}
    {a : (Δ[n] : SSet.{u}) ⟶ I} (j : (sliceUnder a) _⦋0⦌) :
    (joinStdSimplexIso n 0).hom ≫ finiteStageBaseMap (finiteStageSuccessor j) =
      ((finiteStageSourceCosliceIso a).hom.app (Opposite.op ⦋0⦌) (ULift.up j)).val := by
  rw [finiteStageSourceCosliceIso_val]
  dsimp only [finiteStageBaseMap, finiteStageSuccessor]
  rw [Functor.map_comp]
  apply (cancel_epi (joinMap (uliftStdSimplexIso.{u, u + 1} n).hom (𝟙 Δ[0]))).mp
  apply (cancel_epi (uliftCoconeShapeIso.{u, u + 1} (Δ[n] : SSet.{u}) 0).hom).mp
  change (uliftCoconeShapeIso.{u, u + 1} (Δ[n] : SSet.{u}) 0).hom ≫
    joinMap (uliftStdSimplexIso.{u, u + 1} n).hom (𝟙 Δ[0]) ≫
      (joinStdSimplexIso n 0).hom ≫ (uliftStdSimplexIso.{u, u + 1} (n + 1)).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (joinStdSimplexIso n 0).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map j.val =
    (uliftCoconeShapeIso.{u, u + 1} (Δ[n] : SSet.{u}) 0).hom ≫
      joinMap (uliftStdSimplexIso.{u, u + 1} n).hom (𝟙 Δ[0]) ≫
        joinMap (uliftStdSimplexIso.{u, u + 1} n).inv (𝟙 Δ[0]) ≫
          (uliftCoconeShapeIso.{u, u + 1} (Δ[n] : SSet.{u}) 0).inv ≫
            (SSet.uliftFunctor.{u + 1, u}).map j.val
  calc
    _ = ((uliftCoconeShapeIso.{u, u + 1} (Δ[n] : SSet.{u}) 0).hom ≫
        joinMap (uliftStdSimplexIso.{u, u + 1} n).hom (𝟙 Δ[0]) ≫
          (joinStdSimplexIso n 0).hom) ≫
        (uliftStdSimplexIso.{u, u + 1} (n + 1)).inv ≫
          (SSet.uliftFunctor.{u + 1, u}).map (joinStdSimplexIso n 0).inv ≫
            (SSet.uliftFunctor.{u + 1, u}).map j.val := by simp only [Category.assoc]
    _ = (SSet.uliftFunctor.{u + 1, u}).map j.val := by
      rw [← finiteJoinUniverse_naturality n]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
        (SSet.uliftFunctor.{u + 1, u}).map_id (join (Δ[n] : SSet.{u}) Δ[0]),
        Category.id_comp]
    _ = _ := by
      rw [← Category.assoc (joinMap _ _), ← joinMap_comp, Iso.hom_inv_id,
        Category.id_comp, joinMap_id, Category.id_comp, Iso.hom_inv_id_assoc]

/-- 概要：元の小さい後続図式の最終頂点を除く面は元の前置図式。
方針：標準 join 同型の左包含を計算する。
規約：全前置単体を厳密に保持する。
使われ方：元の表示添字内の可算貼り合わせ。 -/
lemma finiteStageSuccessor_front {n : ℕ} {I : SSet.{u}}
    {a : (Δ[n] : SSet.{u}) ⟶ I} (j : (sliceUnder a) _⦋0⦌) :
    SSet.stdSimplex.map (PinchedHom.front n) ≫ finiteStageSuccessor j = a := by
  rw [finiteStageSuccessor, ← joinStdSimplexIso_rightPoint_inl, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact j.property

end SerrePositivity.InfinityCategories.F2.Presentable

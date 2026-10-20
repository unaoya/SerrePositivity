module

public import SerrePositivity.InfinityCategories.F1.CoherentConeHeadWeightedComparison
public import SerrePositivity.InfinityCategories.F1.WeightedKanLeftCutCoslicePrism
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedCosliceComparison

/-!
概要：左切断の時刻零で、元の weighted cone と coslice 比較を厳密に回収する。
方針：全ての正頂点が時刻零であるとき、元の head と tail の式を使う。
規約：対象ごとの同型ではなく、元の全単体と全 prism の厳密な端点を計算する。
使われ方：共通 weighted 始域上の pointed prism の始点の固定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 全頂点が時刻零なら、実際の切断 cone は元の weighted cone そのもの。 -/
lemma weightedKanLeftCutConeSimplex_zero {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (ht : ∀ j, (stdSimplex.objEquiv t).toOrderHom j = 0) :
    weightedKanLeftCutConeSimplex F G x σ τ s t = weightedConeSimplex F.val x τ := by
  exact coherentConeSimplexOfHead_eq_weighted F.val x σ τ _
    (weightedKanLeftCutConeHead F G x σ τ s t)
    (fun j => kanDiagramLeftHomCutSimplex_obj_zero F G σ s t j (ht j))
    (fun j => weightedKanLeftCutHead_zero F G x σ τ s t j (ht j))
    (fun i j hij => weightedKanLeftCutTail_zero F G σ s t i j hij (ht i) (ht j))

/-- 時刻零の coslice 単体は、元の weighted coslice 比較の同じ単体に厳密に一致。 -/
lemma weightedKanLeftCutCosliceSimplex_zero {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌)
    (t : (Δ[1] : SSet.{u + 1}) _⦋n⦌)
    (ht : ∀ j, (stdSimplex.objEquiv t).toOrderHom j = 0) :
    weightedKanLeftCutCosliceSimplex F G x σ τ s t = weightedCosliceSimplex F.val x ⟨σ, τ⟩ := by
  apply Subtype.ext
  exact congrArg (fun A : SpaceInfinity.{u} _⦋n + 1⦌ =>
    (leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm A)
      (weightedKanLeftCutConeSimplex_zero F G x σ τ s t ht)

/-- 全 weighted 係数・全 Hom の prism の始点は、元の weighted coslice 比較そのもの。 -/
lemma weightedKanLeftCutCoslicePrism_zero {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) :
    (prismEndpoint 0 _ ▷ _) ≫ weightedKanLeftCutCoslicePrism F G x =
      fst _ _ ≫ weightedCosliceComparison F.val x := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨⟨σ, τ⟩⟩, s⟩
  exact weightedKanLeftCutCosliceSimplex_zero F G x σ τ s.down _ (fun _ => rfl)

end SerrePositivity.InfinityCategories

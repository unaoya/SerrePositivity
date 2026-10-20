module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentOppositeEdge
public import SerrePositivity.InfinityCategories.HomotopyLimits.FinalHornFilledRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.FinalHornLastEdge
public import SerrePositivity.InfinityCategories.Core.RelativeOuterHornOp

/-!
概要：前合成が trivial Kan な固定初期辺を持つ coherent ホーンを充填する。
方針：反対豊穣圏上の最終ホーンで二つの Hom を延長し、単体を元へ反転する。
規約：反対圏のモデル構造を要求しない。使われ方：元の左 Quillen 辺の coCartesian 性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory SSet
open CategoryTheory.SimplicialThickening
open SerrePositivity.InfinityCategories.Coherent
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

variable {n : ℕ}
  (σ : (Λ[n + 2, 0] : SSet.{max u v}) ⟶ SimplicialNerve C)

/-- 初期ホーンを反対豊穣圏の最終ホーンへ送る。 -/
def initialHornOppositeMap :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ SimplicialNerve Cᵒᵖ :=
  reverseInitialHornMap n σ ≫ (coherentNerveOppositeIso C).hom

/-- 固定初期辺は同じ射の反対を表す固定最終辺になる。 -/
lemma initialHornOppositeMap_edge {X Y : C} (f : X ⟶ Y)
    (h : σ.app (Opposite.op ⦋1⦌) (initialHornEdge n) = (coherentNerveEdge f).edge) :
    (initialHornOppositeMap σ).app (Opposite.op ⦋1⦌) (finalHornEdge n) =
      (coherentNerveEdge f.op).edge := by
  change (coherentNerveOppositeMap C).app _
    ((reverseInitialHornMap n σ).app _ (finalHornEdge n)) = _
  rw [reverseInitialHornMap_edge, h, coherentNerveOppositeMap_edge]

/-- 反対ホーンの対象は、反転した添字の元の対象の反対である。 -/
lemma initialHornOppositeMap_obj (a : Fin (n + 3)) :
    hornObj (initialHornOppositeMap σ) a = Opposite.op (hornObj σ a.rev) := by
  rfl

/-- 元の固定初期辺の前合成条件から、元の初期ホーンの充填を得る。 -/
lemma initialHornFiller_of_precomposition {X Y : C} (f : X ⟶ Y)
    (h : σ.app (Opposite.op ⦋1⦌) (initialHornEdge n) = (coherentNerveEdge f).edge)
    [KanComplex (SimplicialCategory.sHom (hornObj σ 0) (hornObj σ (Fin.last (n + 2))))]
    [TrivialKanFibration (eHomWhiskerRight SSet f (hornObj σ (Fin.last (n + 2))))] :
    ∃ l : (Δ[n + 2] : SSet.{max u v}) ⟶ SimplicialNerve C, (Λ[n + 2, 0]).ι ≫ l = σ := by
  have hKan : KanComplex (SimplicialCategory.sHom
      (hornObj (initialHornOppositeMap σ) 0)
      (hornObj (initialHornOppositeMap σ) (Fin.last (n + 2)))) := by
    rw [initialHornOppositeMap_obj, initialHornOppositeMap_obj, Fin.rev_zero, Fin.rev_last]
    exact inferInstanceAs (KanComplex
      (SimplicialCategory.sHom (hornObj σ 0) (hornObj σ (Fin.last (n + 2)))))
  have hTF : TrivialKanFibration (eHomWhiskerLeft SSet
      (hornObj (initialHornOppositeMap σ) 0) f.op) := by
    rw [initialHornOppositeMap_obj, Fin.rev_zero, eHomWhiskerLeft_op_eq_right]
    infer_instance
  obtain ⟨g, hz, hg, front, hf, hfg⟩ := finalHornUnknownHom_extension_of_fixedEdge
    (initialHornOppositeMap σ) f.op (initialHornOppositeMap_edge σ f h)
  let l' := finalHornFiller (initialHornOppositeMap σ) g front hf hg hfg
  have hl' : (Λ[n + 2, Fin.last (n + 2)]).ι ≫ l' = initialHornOppositeMap σ :=
    finalHornFiller_restriction (initialHornOppositeMap σ) g front hf hg hfg hz
  let lbar := l' ≫ (coherentNerveOppositeIso C).inv
  have hlbar : (Λ[n + 2, Fin.last (n + 2)]).ι ≫ lbar = reverseInitialHornMap n σ := by
    change ((Λ[n + 2, Fin.last (n + 2)]).ι ≫ l') ≫
      (coherentNerveOppositeIso C).inv = _
    rw [hl']
    simp only [initialHornOppositeMap, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let l := reverseSimplex (n + 2) lbar ≫
    (SSet.opFunctorCompOpFunctorIso.app (SimplicialNerve C)).hom
  refine ⟨l, ?_⟩
  apply reverseHornMap_injective (SimplicialNerve C) (n + 2) 0
  rw [reverseHornMap_restrict, reverseSimplex_back]
  apply (cancel_epi (initialHornReverseIndexIso n).hom).1
  rw [← Category.assoc, initialHornReverseIndexIso_hom_ι]
  exact hlbar

end
end SerrePositivity.InfinityCategories.HomotopyLimits

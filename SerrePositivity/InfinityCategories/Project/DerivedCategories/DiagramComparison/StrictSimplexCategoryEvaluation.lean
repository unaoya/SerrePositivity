module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexCategory
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseJoinSimplexShapes

/-!
概要：固定次元の元の HA 単体の通常圏を、全 nerve と同じセル上で同時評価する。
方針：元の単体の Yoneda 図式と厳密写像の引き戻しから、全 HA 族の評価を使う。
規約：同じ小さいセルの宇宙変更は既存の同型を使う。
使われ方：3b-3 R6、各 native セルの全族を既存の slice 普遍性で貼り合わせる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet MonoidalCategory SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 厳密 HA 写像の連続した引き戻しは、元の合成した引き戻しに一致する。 -/
lemma StrictSimplexMap.pullback_pullback {A : Type u} [CommRing A] {E : Type (u + 1)} [DGCategory A E]
    {l m n : ℕ} {s t : SimplexData A E n} (f : StrictSimplexMap A E s t)
    (β : Fin (m + 1) →o Fin (n + 1)) (α : Fin (l + 1) →o Fin (m + 1)) :
    HEq ((f.pullback β).pullback α) (f.pullback (β.comp α)) := by
  apply StrictSimplexMap.hext
  · exact Reindex.pullback_comp s α β
  · exact Reindex.pullback_comp t α β
  · intro i
    rfl

variable (A : Type u) [CommRing A] (E : Type (u + 1)) [DGCategory A E] (n : ℕ)

/-- 固定 HA 単体の、同じ小さい標準セルからの元の Yoneda 図式。 -/
def strictSimplexCellDiagram (s : StrictSimplexCategory A E n) :
    (SSet.uliftFunctor.{u + 1, u}).obj (Δ[n] : SSet.{u}) ⟶ dgNerve A E :=
  (uliftStdSimplexIso.{u, u + 1} n).hom ≫ SSet.yonedaEquiv.symm s.val

/-- 同じセルの全単体は、元の HA 単体の同じ引き戻しである。 -/
lemma strictSimplexCellDiagram_simplex (s : StrictSimplexCategory A E n) {q : ℕ}
    (τ : (Δ[n] : SSet.{u}) _⦋q⦌) :
    coherentDiagramSimplex (strictSimplexCellDiagram A E n s) τ =
      s.val.pullback (stdSimplex.objEquiv τ).toOrderHom := rfl

/-- 固定 HA セルの通常圏全体を動かす、同じ全 HA 成分の厳密な族。 -/
def strictSimplexCellFamily :
    StrictCoherentFamily A E (Δ[n] : SSet.{u}) (StrictSimplexCategory A E n) where
  obj s := strictSimplexCellDiagram A E n s
  map {c d} f {q} τ := f.pullback (stdSimplex.objEquiv τ).toOrderHom
  map_id s {q} τ := StrictSimplexMap.pullback_id s.val.toSimplexData (stdSimplex.objEquiv τ).toOrderHom
  map_comp {c d e} f g {q} τ := StrictSimplexMap.pullback_comp f g (stdSimplex.objEquiv τ).toOrderHom
  map_pullback {c d} f {r q} α τ := by
    change HEq (f.pullback ((stdSimplex.objEquiv τ).toOrderHom.comp α))
      ((f.pullback (stdSimplex.objEquiv τ).toOrderHom).pullback α)
    exact (f.pullback_pullback (stdSimplex.objEquiv τ).toOrderHom α).symm

/-- 全 nerve と元の同じ標準セルを同時に評価する単体的写像。 -/
def strictSimplexCategoryEvaluation :
    nerve (StrictSimplexCategory A E n) ⊗ (Δ[n] : SSet.{u + 1}) ⟶ dgNerve A E :=
  (nerve (StrictSimplexCategory A E n) ◁ (uliftStdSimplexIso.{u, u + 1} n).inv) ≫
    (strictSimplexCellFamily A E n).evaluation

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

module

public import SerrePositivity.InfinityCategories.F1.KanDiagramReflectedHomPostcomposition
public import SerrePositivity.InfinityCategories.F1.WeightedNerveEnriched
public import SerrePositivity.InfinityCategories.F1.WeightedConeCutComposition

/-!
概要：元の weighted 係数と全 Kan 変換を、実際の反転 Hom 作用で合成する。
方針：既存の weighted nerve の全評価を使い、その各係数を明示する。
規約：係数の自然性を追加仮定として受け取らない。
使われ方：左切断 prism の終点の元の weighted 比較への同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 元の全変換の反転 Hom 作用を weighted nerve で評価した、実際の合成係数図式。 -/
def weightedKanHomCompositeDiagram {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌) :
    simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram G.val x ⋙ SSet.opFunctor :=
  ((weightedNerveMappingFamily (simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (simplicialHomDiagram G.val x ⋙ SSet.opFunctor)).app (Opposite.op ⦋n⦌)
      (⟨σ, τ⟩, (kanDiagramReflectedHomPostcomposition F G x).app _ s)).2

/-- 実際の weighted Hom 作用の各係数は、元の二係数を同じ初区間で合成したもの。 -/
lemma weightedKanHomCompositeDiagram_app {I : Type u} [SmallCategory I]
    (F G : KanDiagramObject I) (x : KanObject.{u}) {n : ℕ} (σ : (nerve I) _⦋n⦌)
    (τ : simplexPrefixWeight n ⟶ σ ⋙ simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
    (s : (SimplicialCategory.sHom F G).op _⦋n⦌) (j : Fin (n + 1)) :
    (weightedKanHomCompositeDiagram F G x σ τ s).app j =
    weightedCutCompositeSimplex x (F.val.obj (σ.obj j)) (G.val.obj (σ.obj j)) j (τ.app j)
      (SSet.yonedaEquiv.symm s ≫ SSet.opFunctor.map (strictDiagramMappingComponent
        (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) (σ.obj j))) := by
  let r := kanDiagramReflectedHomPostcomposition F G x
  let a := stdSimplex.map (simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
    SSet.yonedaEquiv.symm s
  change lift (τ.app j) (stdSimplex.map (simplexPrefixInclusion j.val n _) ≫
    SSet.yonedaEquiv.symm (r.app _ s)) ≫ uncurry (strictDiagramMappingComponent
      (simplicialHomDiagram F.val x ⋙ SSet.opFunctor)
      (simplicialHomDiagram G.val x ⋙ SSet.opFunctor) (σ.obj j)) = _
  rw [← SSet.yonedaEquiv_symm_comp s r]
  have h : lift (τ.app j) (stdSimplex.map (simplexPrefixInclusion j.val n _) ≫
      (SSet.yonedaEquiv.symm s ≫ r)) =
    lift (τ.app j) a ≫ ((SimplicialCategory.sHom x (F.val.obj (σ.obj j))).op ◁ r) :=
    (lift_whiskerLeft (τ.app j) a r).symm
  rw [h, Category.assoc, ← uncurry_natural_left]
  rw [show r = kanDiagramReflectedHomPostcomposition F G x from rfl,
    kanDiagramReflectedHomPostcomposition_uncurry]
  rfl

end SerrePositivity.InfinityCategories

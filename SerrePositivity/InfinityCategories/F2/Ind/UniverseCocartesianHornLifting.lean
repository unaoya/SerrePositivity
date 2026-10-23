module

public import SerrePositivity.InfinityCategories.F2.Ind.UniverseHornDiagramDown
public import SerrePositivity.InfinityCategories.F1.Universe.InvertibleEdge

/-!
概要：元の指定 cocartesian 辺の外側ホーン充填条件は宇宙持ち上げで保存される。
方針：同じ最初の辺を保って図式を戻し、元の充填を同じ形状同型で持ち上げる。
規約：モデル構造も充填性の追加仮定も不要。使われ方：weighted 射影の cocartesian 性の宇宙移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open SimplicialModel.UniverseLift

/-- 元の cocartesian 外側ホーンの充填は、同じ持ち上げた辺について成立する。 -/
lemma hasCocartesianHornLifting_ulift {E B : SSet.{u}} (p : E ⟶ B)
    {x y : E _⦋0⦌} (e : SSet.Truncated.Edge (X := (truncation 2).obj E) x y)
    (he : HasCocartesianHornLifting p e) :
    HasCocartesianHornLifting ((SSet.uliftFunctor.{v, u}).map p) (uliftTruncatedEdge.{u, v} e) := by
  intro n σ β hσ hw
  have hι : (SSet.uliftFunctor.{v, u}).map (horn.{u} (n + 2) 0).ι ≫
      (simplexIso.{v, u} ⦋n + 2⦌).hom =
        (hornIso.{v, u} (n + 2) 0).hom ≫ (horn.{max u v} (n + 2) 0).ι := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  have hι' : (horn.{max u v} (n + 2) 0).ι ≫ (simplexIso.{v, u} ⦋n + 2⦌).inv =
      (hornIso.{v, u} (n + 2) 0).inv ≫ (SSet.uliftFunctor.{v, u}).map (horn.{u} (n + 2) 0).ι := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  have hs : (universeHornDiagramDown (n + 2) 0 σ).app (Opposite.op ⦋1⦌)
      (initialHornEdge.{u} n) = e.edge :=
    (universeHornDiagramDown_initialEdge n σ).trans (congrArg ULift.down hσ)
  have hw₀ : universeHornDiagramDown (n + 2) 0 σ ≫ p =
      (horn.{u} (n + 2) 0).ι ≫ universeSimplexDiagramDown (n + 2) β := by
    apply (SSet.uliftFunctor.{v, u}).map_injective
    rw [CategoryTheory.Functor.map_comp, universeHornDiagramDown_map,
      CategoryTheory.Functor.map_comp, universeSimplexDiagramDown_map]
    rw [Category.assoc, hw, ← Category.assoc, ← hι, Category.assoc]
  obtain ⟨φ, hφ, hφp⟩ := he n (universeHornDiagramDown (n + 2) 0 σ)
    (universeSimplexDiagramDown (n + 2) β) hs hw₀
  refine ⟨(simplexIso.{v, u} ⦋n + 2⦌).inv ≫ (SSet.uliftFunctor.{v, u}).map φ, ?_, ?_⟩
  · rw [← Category.assoc, hι', Category.assoc, ← CategoryTheory.Functor.map_comp,
      hφ, universeHornDiagramDown_map, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hφp,
      universeSimplexDiagramDown_map, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.F2.Ind

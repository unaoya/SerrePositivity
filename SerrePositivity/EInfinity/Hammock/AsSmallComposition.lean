module

public import SerrePositivity.EInfinity.Hammock.AsSmallArrow
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeAppendFunctor
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PointActions

/-!
概要：元の AsSmall hammock 同型は同じ全合成と全標的の後合成を保持する。
方針：元の全語の標準射の共同全射性と連結関手の自然性を使う。
規約：同じ実同型・元の全単体を保持する。
使われ方：strict Kan Hom 図式を同じ balanced hammock の豊穣 Hom に同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.AsSmallComparison
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X Y Z : C} {n : SimplexCategoryᵒᵖ}

/-- 概要：元の固定語の点は同じ AsSmall 語の点に写る。
方針：同じ標準射との可換性を評価する。
規約：元の点の表示を保持。使われ方：全合成の照合。 -/
lemma colimitIso_graph_point {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y).obj n) :
    (colimitIso W X Y).hom.app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app n σ) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weak W) (AsSmall.up.obj X) (AsSmall.up.obj Y) a).app n
        (σ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (up W)) :=
  congrArg (fun k => k.app n σ) (graphInclusion_colimitIso W X Y a)

/-- 概要：同じ AsSmall 比較は元の余極限の全合成を保持する。
方針：全語の二つの標準射へ制限し、元の連結関手の自然性を使う。
規約：全点と同じ実比較。使われ方：全標的の後合成の整合。 -/
lemma colimitIso_composePoint (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y).obj n)
    (q : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z).obj n) :
    (colimitIso W X Z).hom.app n (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint W X Y Z p q) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint (weak W) (AsSmall.up.obj X) (AsSmall.up.obj Y) (AsSmall.up.obj Z)
        ((colimitIso W X Y).hom.app n p) ((colimitIso W Y Z).hom.app n q) := by
  obtain ⟨a, σ, hp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y) n p
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a).app n σ = p at hp
  cases hp
  obtain ⟨b, τ, hq⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W Y Z) n q
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b).app n τ = q at hq
  cases hq
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions, colimitIso_graph_point, colimitIso_graph_point,
    colimitIso_graph_point, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint_inclusions]
  apply congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion (weak W) (AsSmall.up.obj X)
    (AsSmall.up.obj Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b)).app n)
  rw [CategoryTheory.Functor.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_functor]
  rfl

/-- 概要：同じ AsSmall 同型は元の射による後合成と全単体で可換。
方針：同じ全合成と元の forward 射の照合を使う。
規約：実自然性の等式。使われ方：全 Hom 族の自然同型。 -/
lemma colimitIso_postcompose (f : Y ⟶ Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f) ≫ (colimitIso W X Z).hom =
      (colimitIso W X Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.postcomposePointMap (AsSmall.up.obj X) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap (weak W) (AsSmall.up.map f)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  have h := colimitIso_composePoint W p ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap W f).app n PUnit.unit)
  have ha := congrArg (fun a => a.app n PUnit.unit) (arrowMap_colimitIso W f)
  change _ = _ at h
  exact h.trans (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.composePoint (weak W) (AsSmall.up.obj X)
    (AsSmall.up.obj Y) (AsSmall.up.obj Z) ((colimitIso W X Y).hom.app n p)) ha)

end SerrePositivity.EInfinity.Hammock.AsSmallComparison

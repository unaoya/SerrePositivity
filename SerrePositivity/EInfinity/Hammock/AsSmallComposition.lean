module

public import SerrePositivity.EInfinity.Hammock.AsSmallArrow
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeAppendFunctor
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitCompositionPoints
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitPoints
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.PointActions

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
lemma colimitIso_graph_point {a : Word} (σ : (graph W a X Y).obj n) :
    (colimitIso W X Y).hom.app n ((graphInclusion W X Y a).app n σ) =
      (graphInclusion (weak W) (AsSmall.up.obj X) (AsSmall.up.obj Y) a).app n
        (σ ⋙ Zigzag.Relative.functor (up W)) :=
  congrArg (fun k => k.app n σ) (graphInclusion_colimitIso W X Y a)

/-- 概要：同じ AsSmall 比較は元の余極限の全合成を保持する。
方針：全語の二つの標準射へ制限し、元の連結関手の自然性を使う。
規約：全点と同じ実比較。使われ方：全標的の後合成の整合。 -/
lemma colimitIso_composePoint (p : (colimitGraph W X Y).obj n)
    (q : (colimitGraph W Y Z).obj n) :
    (colimitIso W X Z).hom.app n (composePoint W X Y Z p q) =
      composePoint (weak W) (AsSmall.up.obj X) (AsSmall.up.obj Y) (AsSmall.up.obj Z)
        ((colimitIso W X Y).hom.app n p) ((colimitIso W Y Z).hom.app n q) := by
  obtain ⟨a, σ, hp⟩ := colimit_point_surjective (graphDiagram W X Y) n p
  change (graphInclusion W X Y a).app n σ = p at hp
  cases hp
  obtain ⟨b, τ, hq⟩ := colimit_point_surjective (graphDiagram W Y Z) n q
  change (graphInclusion W Y Z b).app n τ = q at hq
  cases hq
  rw [composePoint_inclusions, colimitIso_graph_point, colimitIso_graph_point,
    colimitIso_graph_point, composePoint_inclusions]
  apply congrArg ((graphInclusion (weak W) (AsSmall.up.obj X)
    (AsSmall.up.obj Z) (Word.append a b)).app n)
  rw [CategoryTheory.Functor.assoc, Zigzag.Relative.append_functor]
  rfl

/-- 概要：同じ AsSmall 同型は元の射による後合成と全単体で可換。
方針：同じ全合成と元の forward 射の照合を使う。
規約：実自然性の等式。使われ方：全 Hom 族の自然同型。 -/
lemma colimitIso_postcompose (f : Y ⟶ Z) :
    postcomposePointMap X (arrowMap W f) ≫ (colimitIso W X Z).hom =
      (colimitIso W X Y).hom ≫
        postcomposePointMap (AsSmall.up.obj X) (arrowMap (weak W) (AsSmall.up.map f)) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  have h := colimitIso_composePoint W p ((arrowMap W f).app n PUnit.unit)
  have ha := congrArg (fun a => a.app n PUnit.unit) (arrowMap_colimitIso W f)
  change _ = _ at h
  exact h.trans (congrArg (composePoint (weak W) (AsSmall.up.obj X)
    (AsSmall.up.obj Y) (AsSmall.up.obj Z) ((colimitIso W X Y).hom.app n p)) ha)

end SerrePositivity.EInfinity.Hammock.AsSmallComparison

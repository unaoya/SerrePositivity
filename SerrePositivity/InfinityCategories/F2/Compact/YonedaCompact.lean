module
public import SerrePositivity.InfinityCategories.F2.Compact.Preservation

public import SerrePositivity.InfinityCategories.F2.Compact.UniverseColimits
public import SerrePositivity.InfinityCategories.Core.Compact.UniverseCoconePostcomposition
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafPointwiseColimits

/-!
概要：元の前層 ∞ 圏の同じ Yoneda 像は κ-compact。
方針：元の全共変 Hom と評価・指定宇宙変更の全自然同型に、小余極限保存を合成する。
規約：元の全 Hom による定義と元の指定余極限余錐を保持。HTT 5.3.5.5。
使われ方：Ind 内の表現可能前層の compact 性と元の Yoneda retract 閉包との比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {C : SSet.{u}} [Quasicategory C]

omit [Quasicategory C] in
/-- 元の評価と指定した同じ宇宙変更の合成は、小さい κ-filtered 余極限を保存する。 -/
lemma presheafEvaluationUniverse_preservesKappaFilteredColimits
    (κ : Cardinal.{u}) (y : C _⦋0⦌) :
    PreservesKappaFilteredColimits.{u, u + 1} κ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (presheafInfinityEvaluation y) ≫
        spaceUniverseDiagram.{u}) := by
  intro I hI hFiltered D c hc
  rw [mapJoinCocone_universe_comp]
  exact spaceUniverseDiagram_map_isColimit (D ≫ presheafInfinityEvaluation y) _
    (presheafInfinity_evaluation_isColimit D c hc y)

/-- 元の表現可能前層の指定頂点は、元の全共変 Hom の意味で κ-compact。 -/
lemma representablePresheafInfinity_isKappaCompact (κ : Cardinal.{u}) (y : C _⦋0⦌) :
    IsKappaCompact.{u, u + 1} κ (functorVertex (representablePresheafInfinity y)) :=
  (presheafEvaluationUniverse_preservesKappaFilteredColimits κ y).of_functorIso
    (yonedaEvaluation_universeIso y).symm

/-- 元の Yoneda 埋め込みの同じ実頂点は κ-compact。 -/
lemma yonedaInfinityMap_isKappaCompact (κ : Cardinal.{u}) (y : C _⦋0⦌) :
    IsKappaCompact.{u, u + 1} κ
      ((yonedaInfinityMap C).app (Opposite.op ⦋0⦌) (ULift.up y)) := by
  rw [yonedaInfinityMap_vertex]
  exact representablePresheafInfinity_isKappaCompact κ y

end SerrePositivity.InfinityCategories.F2.Compact

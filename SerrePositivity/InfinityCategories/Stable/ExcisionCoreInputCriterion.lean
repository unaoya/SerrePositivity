module
public import SerrePositivity.InfinityCategories.Stable.ExcisionCoreCanonicalComparison
public import SerrePositivity.InfinityCategories.Stable.PullbackComparisonReflection
public import Mathlib.CategoryTheory.EpiMono

/-!
概要：同じ実比較辺を元の θ と照合し、対角の可逆性から入力面の普遍性へ戻す。
方針：全錐の写像と射影辺を保つ等号輸送、錐の圏の終性、右 fibration の反映を使う。
規約：一般安定性は仮定しない。使われ方：HA 1.4.2.15 の二条件からの切除判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

private lemma iso_of_neighbor_composites {C : Type*} [Category C]
    {W X Y Z : C} (a : W ⟶ X) (f : X ⟶ Y) (b : Y ⟶ Z)
    [IsIso (a ≫ f)] [IsIso (f ≫ b)] : IsIso f := by
  have : Mono f := mono_of_mono f b
  have : IsSplitEpi f := IsSplitEpi.mk' ⟨inv (a ≫ f) ≫ a, by simp [Category.assoc]⟩
  exact isIso_of_mono_of_isSplitEpi f

lemma excisionCoreInput_isPullback_of_comparison_factors {X : SSet.{u}} [Quasicategory X]
    (F : nerve ExcisionGridCoreIndex.{u} ⟶ X)
    (d : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)))
    (hd : IsLimitCone d)
    (e : JoinCone (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)))
    (he : IsLimitCone e)
    (a : Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2))))
        (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 2 2)) d)
    (b : Truncated.Edge (X := (truncation 2).obj
      (sliceOver (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))
        (pullbackCone (grid22Face (excisionGridCoreDiagram ≫ F) 1 1)) e)
    (hb : IsInvertibleEdge (b.map ((truncation 2).map (sliceOverProjection
      (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))))))
    {z : hoFunctor.obj X}
    (v : (HomotopyCategory.mk e.vertex : hoFunctor.obj X) ⟶ z)
    (hv : IsIso (Truncated.HomotopyCategory.homMk
      (excisionCoreComparisonEdge F d hd e he) ≫ v)) :
    IsPullbackSquare (grid22Face (excisionGridCoreDiagram ≫ F) 2 2) := by
  let qi := sliceOverProjection
    (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 2 2))
  let qo := sliceOverProjection
    (pullbackCospan (grid22Face (excisionGridCoreDiagram ≫ F) 1 1))
  let af := Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map qi))
  let t := Truncated.HomotopyCategory.homMk (excisionCoreComparisonEdge F d hd e he)
  have h := excisionCoreComparisonEdge_canonical_composite_of_edges F d hd e he a b
  dsimp only at h
  have : IsIso (Truncated.HomotopyCategory.homMk (b.map ((truncation 2).map qo))) := hb
  have : IsIso (af ≫ t) := by
    change IsIso (Truncated.HomotopyCategory.homMk (a.map ((truncation 2).map qi)) ≫
      Truncated.HomotopyCategory.homMk (excisionCoreComparisonEdge F d hd e he))
    rw [h]
    infer_instance
  have : IsIso (t ≫ v) := hv
  have : IsIso t := iso_of_neighbor_composites af t v
  have : IsIso af := IsIso.of_isIso_comp_right af t
  exact isPullbackSquare_of_invertible_coneComparison _ d hd a this

end SerrePositivity.InfinityCategories

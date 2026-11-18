module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.StrictCoconeEdgeReflection
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCocones.CoconeTriangleReverseShape
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrdinaryCoherentReversal
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.StrictConeSimplex

/-!
概要：通常の指定余錐の一辺と二脚を、元の通常の合成二単体の coherent 表示へ同定する。
方針：反対の錐の全単体の式を反転して戻し、同じ射列の反対同値を用いる。
規約：三つの辺だけでなく指定した二単体全体を保つ。
使われ方：HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、S8 の元の押し出し四角形。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {I : Type u} [SmallCategory I] {C : Type v}
  [Category.{u} C] [SimplicialCategory C] {F : I ⥤ C} {i j : I}

private lemma oppositePrecompArrow (f : i ⟶ j) {z : C} (g : F.obj j ⟶ z) :
    ComposableArrows.precomp (ComposableArrows.mk₁ f.op ⋙ F.op) g.op =
      (ComposableArrows.opEquivalence C 2).functor.obj
        (Opposite.op (ComposableArrows.mk₂ (F.map f) g)) := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro k
    fin_cases k <;> rfl
  · intro k l h
    fin_cases k <;> fin_cases l
    all_goals first
    | rfl
    | solve
      | have hh := leOfHom h
        norm_num at hh
    | apply heq_of_eq
      have hId : h = 𝟙 _ := Subsingleton.elim _ _
      subst h
      simp only [CategoryTheory.Functor.map_id]
      rfl

/-- 反対の錐の一辺上の全三角形は、元の合成二単体の反対の表示。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、全三角形比較の証明分割。 -/
lemma strictCocone_opposite_triangle_val (c : Cocone F) (f : i ⟶ j) :
    (pointJoinStdSimplexIso 1).inv ≫
        joinMap (𝟙 Δ[0])
          (SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₁ f.op)) :
            (Δ[1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve Iᵒᵖ)) ≫
        (strictCoherentCone c.op).val =
      SSet.yonedaEquiv.symm ((nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋2⦌)
        ((ComposableArrows.opEquivalence C 2).functor.obj
          (Opposite.op (ComposableArrows.mk₂ (F.map f) (c.ι.app j))))) := by
  change (pointJoinStdSimplexIso 1).inv ≫ _ ≫ strictCoherentConeMap c.op = _
  rw [strictCoherentConeMap_simplex]
  rw [Iso.inv_hom_id_assoc]
  have ha : SSet.yonedaEquiv
      (SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₁ f.op)) :
        (Δ[1] : SSet.{max u v}) ⟶ (SSet.uliftFunctor.{v, u}).obj (nerve Iᵒᵖ)) =
      ULift.up (ComposableArrows.mk₁ f.op) := SSet.yonedaEquiv.apply_symm_apply _
  rw [ha]
  change SSet.yonedaEquiv.symm ((nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋2⦌)
      (ComposableArrows.precomp (ComposableArrows.mk₁ f.op ⋙ F.op) (c.ι.app j).op)) = _
  rw [oppositePrecompArrow]

/-- 通常の指定余錐の一辺と二脚を切り出すと、同じ通常の合成二単体が得られる。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）。頂点・脚だけの比較ではない。 -/
lemma strictNativeCocone_triangle_val (c : Cocone F) (f : i ⟶ j) :
    strictCoconeLegTriangleShape.{u, v} f ≫ (strictNativeCocone c).val =
      SSet.yonedaEquiv.symm ((nerveToCoherent C).app (Opposite.op ⦋2⦌)
        (ComposableArrows.mk₂ (F.map f) (c.ι.app j))) := by
  let a : (Δ[1] : SSet.{max u v}) ⟶
      (SSet.uliftFunctor.{v, u}).obj (nerve Iᵒᵖ) :=
    SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₁ f.op))
  have hs : strictCoconeLegTriangleShape.{u, v} f ≫
      (joinMap (strictCoconeIndexIso.{u, v} I).hom (𝟙 Δ[0]) ≫
        (strictCoherentCone c.op).reverseCocone.val) =
    (stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map
      ((pointJoinStdSimplexIso 1).inv ≫ joinMap (𝟙 Δ[0]) a ≫
        (strictCoherentCone c.op).val) := by
    change ((joinStdSimplexIso 1 0).inv ≫
        joinMap (SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₁ f))) (𝟙 Δ[0])) ≫
      (joinMap (strictCoconeIndexIso.{u, v} I).hom (𝟙 Δ[0]) ≫
        (strictCoherentCone c.op).reverseCocone.val) = _
    have hj : joinMap (SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₁ f)))
        (𝟙 Δ[0]) ≫ joinMap (strictCoconeIndexIso.{u, v} I).hom (𝟙 Δ[0]) =
      joinMap ((stdSimplex.opIso ⦋1⦌).inv ≫ SSet.opFunctor.map a) (𝟙 Δ[0]) := by
      rw [← joinMap_comp, Category.id_comp, strictCoconeIndexIso_edge]
    rw [Category.assoc, ← Category.assoc
      (joinMap (SSet.yonedaEquiv.symm (ULift.up (ComposableArrows.mk₁ f))) (𝟙 Δ[0]))
      (joinMap (strictCoconeIndexIso.{u, v} I).hom (𝟙 Δ[0]))
      (strictCoherentCone c.op).reverseCocone.val, hj, ← Category.assoc]
    exact reverseCocone_triangle_val (strictCoherentCone c.op) a
  rw [strictNativeCocone_val]
  unfold strictCoherentCocone
  rw [coherentCoconePost_val]
  change (strictCoconeLegTriangleShape.{u, v} f ≫
    (joinMap (strictCoconeIndexIso.{u, v} I).hom (𝟙 Δ[0]) ≫
      (strictCoherentCone c.op).reverseCocone.val)) ≫ (coherentOppositeReturnIso C).hom = _
  rw [hs]
  change ((stdSimplex.opIso ⦋2⦌).inv ≫ SSet.opFunctor.map
    ((pointJoinStdSimplexIso 1).inv ≫ joinMap (𝟙 Δ[0]) a ≫
      (strictCoherentCone c.op).val)) ≫ (coherentOppositeReturnIso C).hom = _
  rw [strictCocone_opposite_triangle_val]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, stableReverseSimplex_yoneda]
  simp only [_root_.Equiv.apply_symm_apply]
  change (coherentOppositeReturnIso C).hom.app (Opposite.op ⦋2⦌)
      (SSet.opObjEquiv.symm ((nerveToCoherent Cᵒᵖ).app (Opposite.op ⦋2⦌)
        ((ComposableArrows.opEquivalence C 2).functor.obj
          (Opposite.op (ComposableArrows.mk₂ (F.map f) (c.ι.app j)))))) = _
  exact coherentOppositeReturnIso_ordinary _

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

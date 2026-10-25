module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ColimitCoconeCompletion
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramYoneda
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteColimitCoconeFamily

/-!
概要：C の元の全余錐族を、元の Ind Yoneda の全余錐族へ移す。
方針：全図式 Yoneda と実余錐形状の宇宙同型を合成する。
規約：元の全族と下方図式への厳密な制限を保持する。
使われ方：有限余極限全余錐族の filtered 補完。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {A K C : SSet.{u}} [Quasicategory C]

/-- 元の C 全余錐族を、同じ全パラメーターの Ind 全余錐族へ移す。 -/
def indYonedaCoconeFamily (l : A ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C) :
    (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      (ihom (join ((SSet.uliftFunctor.{u + 1, u}).obj K) (Δ[0] : SSet.{u + 1}))).obj
        (IndInfinity κ C) :=
  (SSet.uliftFunctor.{u + 1, u}).map l ≫ diagramYoneda κ (join K Δ[0]) C ≫
    (pre (uliftCoconeShapeIso.{u, u + 1} K 0).inv).app (IndInfinity κ C)

/-- 元の全余錐族の下方制限は、元の C 全図式への Yoneda の作用そのもの。 -/
lemma indYonedaCoconeFamily_restriction
    (l : A ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C) :
    indYonedaCoconeFamily κ l ≫
      coconeRestriction ((SSet.uliftFunctor.{u + 1, u}).obj K) (IndInfinity κ C) =
      (SSet.uliftFunctor.{u + 1, u}).map (l ≫ coconeRestriction K C) ≫
        diagramYoneda κ K C := by
  unfold indYonedaCoconeFamily coconeRestriction
  simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
    uliftCoconeShapeIso_inv_inl]
  rw [← diagramYoneda_restrict, ← Category.assoc, ← Functor.map_comp]

/-- 各値の読み戻した全余錐は、同じ C 全余錐の宇宙持ち上げの Ind Yoneda 像。 -/
lemma indYonedaCoconeFamily_vertex_val
    (l : A ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C) (a : A _⦋0⦌) :
    (functorVertexCocone ((indYonedaCoconeFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a))).val =
      (mapJoinCocone (indYoneda κ C)
        (JoinCocone.ulift.{u, u + 1} (kanCoconeFamilyAt l a))).val := by
  change (functorVertexEquiv _ _).symm
    (((pre (uliftCoconeShapeIso.{u, u + 1} K 0).inv).app (IndInfinity κ C)).app _
      ((diagramYoneda κ (join K Δ[0]) C).app _ (ULift.up (l.app _ a)))) = _
  have hv := diagramYoneda_vertex κ (kanCoconeFamilyAt l a).val
  rw [kanCoconeFamilyAt_vertex l a] at hv
  rw [hv, functorVertexMap_precomp]
  rfl

/-- 元の Ind Yoneda 像の普遍性は、同じ全族の各値で回収される。 -/
lemma indYonedaCoconeFamily_isColimit
    (l : A ⟶ (ihom (join K (Δ[0] : SSet.{u}))).obj C)
    (hl : ∀ a, IsColimitCone (mapJoinCocone (indYoneda κ C)
      (JoinCocone.ulift.{u, u + 1} (kanCoconeFamilyAt l a)))) (a : A _⦋0⦌) :
    IsColimitCone (functorVertexCocone ((indYonedaCoconeFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a))) :=
  (isColimitCone_iff_of_coconeMap_eq _ _ (indYonedaCoconeFamily_vertex_val κ l a)).mpr (hl a)

end SerrePositivity.InfinityCategories.F2.Ind

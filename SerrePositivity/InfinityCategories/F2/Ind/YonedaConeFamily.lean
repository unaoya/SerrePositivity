module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.F2.Ind.DiagramYoneda
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteLimitConeFamily

/-!
概要：C の元の全錐族を、元の Ind Yoneda の全錐族へ移す。
方針：全図式 Yoneda の作用を、実錐形状の宇宙同型で前合成する。
規約：元の全族と下方図式への厳密な制限を保持する。
使われ方：有限極限錐族の filtered 補完と元の図式表示の照合。
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

/-- 同じ C 全錐族に対する、実錐形状を揃えた全 Ind Yoneda 族。 -/
def indYonedaConeFamily (l : A ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj C) :
    (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      (ihom (join (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K))).obj
        (IndInfinity κ C) :=
  (SSet.uliftFunctor.{u + 1, u}).map l ≫ diagramYoneda κ (join Δ[0] K) C ≫
    (pre (uliftConeShapeIso.{u, u + 1} K 0).inv).app (IndInfinity κ C)

/-- 元の全錐族の下方への制限は、同じ下方 C 全図式への Yoneda の作用そのもの。 -/
lemma indYonedaConeFamily_restriction
    (l : A ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj C) :
    indYonedaConeFamily κ l ≫
      coneRestriction ((SSet.uliftFunctor.{u + 1, u}).obj K) (IndInfinity κ C) =
      (SSet.uliftFunctor.{u + 1, u}).map (l ≫ coneRestriction K C) ≫
        diagramYoneda κ K C := by
  unfold indYonedaConeFamily coneRestriction
  simp only [Category.assoc, ← NatTrans.comp_app, ← pre_map,
    uliftConeShapeIso_inv_inr]
  rw [← diagramYoneda_restrict, ← Category.assoc, ← Functor.map_comp]

/-- 各値で読み戻した全錐は、元の C 全錐の宇宙持ち上げと Ind Yoneda の合成。 -/
lemma indYonedaConeFamily_vertex_val
    (l : A ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj C) (a : A _⦋0⦌) :
    (functorVertexCone ((indYonedaConeFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a))).val =
      (mapJoinCone (indYoneda κ C)
        (JoinCone.ulift.{u, u + 1} (kanConeFamilyAt l a))).val := by
  change (functorVertexEquiv _ _).symm
    (((pre (uliftConeShapeIso.{u, u + 1} K 0).inv).app (IndInfinity κ C)).app _
      ((diagramYoneda κ (join Δ[0] K) C).app _ (ULift.up (l.app _ a)))) = _
  have hv := diagramYoneda_vertex κ (kanConeFamilyAt l a).val
  rw [kanConeFamilyAt_vertex l a] at hv
  rw [hv, functorVertexMap_precomp]
  change (uliftConeShapeIso.{u, u + 1} K 0).inv ≫
    ((SSet.uliftFunctor.{u + 1, u}).map (kanConeFamilyAt l a).val ≫ indYoneda κ C) = _
  rfl

/-- C の全極限錐族は、包含後も各値で元の全極限錐となる。 -/
lemma indYonedaConeFamily_inclusion_isLimit
    (l : A ⟶ (ihom (join (Δ[0] : SSet.{u}) K)).obj C)
    (hl : ∀ a, IsLimitCone (kanConeFamilyAt l a)) (a : A _⦋0⦌) :
    IsLimitCone (mapJoinCone (indInclusionPresheaf κ C)
      (functorVertexCone ((indYonedaConeFamily κ l).app
        (Opposite.op ⦋0⦌) (ULift.up a)))) := by
  let c := functorVertexCone ((indYonedaConeFamily κ l).app
    (Opposite.op ⦋0⦌) (ULift.up a))
  let d := mapJoinCone (yonedaInfinityMap C) (JoinCone.ulift.{u, u + 1}
    (kanConeFamilyAt l a))
  have he : (mapJoinCone (indInclusionPresheaf κ C) c).val = d.val := by
    change c.val ≫ indInclusionPresheaf κ C = d.val
    rw [show c.val = _ from indYonedaConeFamily_vertex_val κ l a]
    change (_ ≫ indYoneda κ C) ≫ indInclusionPresheaf κ C = _
    rw [Category.assoc, indYoneda_inclusion]
    rfl
  have hd := (mapJoinCone (indInclusionPresheaf κ C) c).property.symm.trans
    ((congrArg (fun f ↦ joinInr (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj K) ≫ f) he).trans d.property)
  exact (isLimitCone_iff_of_diagram_eq (d := d) hd he).mpr
    (yonedaInfinityMap_isLimit _ (hl a))

end SerrePositivity.InfinityCategories.F2.Ind

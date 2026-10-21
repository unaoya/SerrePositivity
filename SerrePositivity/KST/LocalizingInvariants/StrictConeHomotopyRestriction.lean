module

public import SerrePositivity.KST.LocalizingInvariants.StrictConeHomotopy

/-!
概要：錐比較の coherent ホモトピーは、底図式で元の自然変換の prism そのものに制限する。
方針：join の右包含と始対象錐の制限を計算し、自然変換の各射列を照合する。
規約：全区間の等号。使われ方：cospan 比較を固定した fiber cube の一意性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.F2
open SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.LocalizingInvariants.StrictConeMap

lemma shape_inr (I : Type u) [SmallCategory I] :
    joinInr (Δ[0] : SSet.{max u v}) _ ≫ shape.{u, v} I =
      (nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl := by
  rw [shape, ← Category.assoc, joinInr_joinMap, Category.assoc, nerveInitialCone_inr,
    Category.comp_id]

variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C]
  [SimplicialCategory C] {F G : I ⥤ C} (η : F ⟶ G) (c : Cone F) (d : Cone G)
  (m : c.pt ⟶ d.pt) (hm : ∀ i, c.π.app i ≫ η.app i = m ≫ d.π.app i)

lemma prism_restrict :
    ((Δ[1] : SSet.{max u v}) ◁
      ((nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl)) ≫
        largeCoherentPrism (transformation η c d m hm) = strictCoherentNatTransMap η := by
  have ho (r : Fin 2) (i : I) :
      ((ComposableArrows.mk₁ (transformation η c d m hm)).obj r).obj
          (WithInitial.of (AsSmall.up.obj i)) = ((ComposableArrows.mk₁ η).obj r).obj i := by
    fin_cases r <;> rfl
  have hh {r s : Fin 2} (t : r ⟶ s) {i j : I} (f : i ⟶ j) :
      HEq ((Functor.uncurry.obj (ComposableArrows.mk₁ (transformation η c d m hm))).map
        (X := (r, WithInitial.of (AsSmall.up.obj i)))
        (Y := (s, WithInitial.of (AsSmall.up.obj j)))
        (t, WithInitial.incl.map (AsSmall.up.map f)))
        ((Functor.uncurry.obj (ComposableArrows.mk₁ η)).map
          (X := (r, i)) (Y := (s, j)) (t, f)) := by
    fin_cases r <;> fin_cases s
    · rfl
    · rfl
    · have ht : (1 : Fin 2) ≤ 0 := leOfHom t
      exact False.elim (by omega)
    · rfl
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, ⟨s⟩⟩
  change enrichedFunctorOfOrderDiagram _ = enrichedFunctorOfOrderDiagram _
  congr 1
  apply CategoryTheory.Functor.hext
  · intro i
    change ((ComposableArrows.mk₁ (transformation η c d m hm)).obj
      ((stdSimplex.objEquiv t).toOrderHom i.down)).obj
        (WithInitial.of (AsSmall.up.obj (s.obj i.down))) =
      ((ComposableArrows.mk₁ η).obj ((stdSimplex.objEquiv t).toOrderHom i.down)).obj _
    exact ho _ _
  · intro i j f
    have hij : i ≤ j := leOfHom f
    exact hh ((stdSimplex.objEquiv t).toOrderHom.toFunctor.map
      (homOfLE (show i.down ≤ j.down from hij)))
        (s.map (homOfLE (show i.down ≤ j.down from hij)))

lemma homotopy_base :
    (joinInr (Δ[0] : SSet.{max u v}) _ ▷ (Δ[1] : SSet.{max u v})) ≫
        (homotopy η c d m hm).h =
      (β_ ((SSet.uliftFunctor.{v, u}).obj (nerve I)) Δ[1]).hom ≫
        strictCoherentNatTransMap η := by
  change (joinInr _ _ ▷ Δ[1]) ≫ ((shape I ▷ Δ[1]) ≫
    ((β_ _ Δ[1]).hom ≫ largeCoherentPrism (transformation η c d m hm))) = _
  rw [← Category.assoc, ← comp_whiskerRight, shape_inr, ← Category.assoc,
    BraidedCategory.braiding_naturality_left, Category.assoc, prism_restrict]

end SerrePositivity.KST.LocalizingInvariants.StrictConeMap

module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseRightKanCanonical
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanOppositeCanonicalLimits
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaLeftKanHomCanonical
public import SerrePositivity.InfinityCategories.HomotopyLimits.PresheafHomWeights

/-!
概要：元の P_Σ 左 Kan 延長の全共同 Hom 族は、持ち上げた元の Yoneda の右 Kan 延長。
方針：元の標準全余錐を反転し、同じ全 Hom 錐と局所添字の宇宙同型を使う。
規約：全係数を持つ元の共同 Hom 関手と、元の反転した Yoneda 自身を保持する。
使われ方：延長の全自然 Hom 表示を、右 Kan 延長の全自然比較へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の延長の全共同 Hom 族自身は、持ち上げた元の Yoneda の実際の右 Kan 延長。 -/
lemma sigmaLeftKanHom_isRightKanExtension {C : SSet.{u}} [Quasicategory C]
    {D : SSet.{u + 1}} [Quasicategory D]
    {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ D}
    {G : SigmaPresheafInfinity C ⟶ D}
    (β : SSet.Homotopy F₀ (sigmaYonedaInfinityMap C ≫ G))
    (hβ : IsLeftKanExtension (sigmaYonedaInfinityMap C) F₀ G β) :
    IsRightKanExtension
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (sigmaYonedaInfinityMap C)))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (sigmaYonedaInfinityMap C)) ≫
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map G) ≫ coyonedaInfinityMap D))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map G) ≫ coyonedaInfinityMap D)
      (functorHomotopyRefl
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (sigmaYonedaInfinityMap C)) ≫
          ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map G) ≫
            coyonedaInfinityMap D))) := by
  apply rightKanExtension_refl_post_ulift_of_canonicalLimits
  intro c
  have h := rightKanCanonicalCone_op_isLimit (sigmaYonedaInfinityMap C) G
    (SSet.opObjEquiv c) (sigmaLeftKanExtension_canonicalColimits β hβ (SSet.opObjEquiv c))
  have he : SSet.opObjEquiv.symm (SSet.opObjEquiv c) = c := Equiv.symm_apply_apply _ c
  rw [he] at h
  exact coyonedaInfinityMap_map_isLimit _ h

end SerrePositivity.InfinityCategories.HomotopyLimits

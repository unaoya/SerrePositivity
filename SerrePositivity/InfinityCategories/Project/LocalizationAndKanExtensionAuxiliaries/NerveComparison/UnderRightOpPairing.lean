module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderOppositePairing
/-! 同じ元のpairingの添字表示・前合成・係数移送の厳密な照合。 -/

@[expose] public section
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison

lemma nerveUnderLift_rightOp_pairing {I C : Type u} [Category.{u} I] [Category.{u} C]
    {c : C} {V : Iᵒᵖ ⥤ C} (η : V ⟶ (Functor.const Iᵒᵖ).obj c) :
    nerveMap (Under.lift (X := Opposite.op c) V.rightOp (NatTrans.rightOp η)) ≫ nerveUnderMap (Opposite.op c) ≫
      cosliceTwistedArrowMap (nervePoint (Opposite.op c)) ≫
        edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
          twistedArrowOppositeSwap (nerve C) =
      twistedPairingNerveMap V.rightOp ((Functor.const I).obj c)
        (fun i => η.app (Opposite.op i)) (by
          intro i j f
          change V.map f.op ≫ η.app (Opposite.op i) ≫ 𝟙 c = η.app (Opposite.op j)
          calc
            _ = V.map f.op ≫ η.app (Opposite.op i) := congrArg (fun g => V.map f.op ≫ g)
              (Category.comp_id (η.app (Opposite.op i)))
            _ = η.app (Opposite.op j) := (η.naturality f.op).trans (Category.comp_id _)) := by
  have hp := nerveUnderLift_comp_cosliceTwistedArrowMap (c := Opposite.op c)
    (V := V.rightOp) (NatTrans.rightOp η)
  have hx := congrArg (fun f : nerve I ⟶ TwistedArrow (nerve Cᵒᵖ) =>
    f ≫ edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
      twistedArrowOppositeSwap (nerve C)) hp
  have h := twistedPairingNerveMap_opposite_swap V.rightOp ((Functor.const I).obj c)
    (fun i => η.app (Opposite.op i)) (by
      intro i j f
      change V.map f.op ≫ η.app (Opposite.op i) ≫ 𝟙 c = η.app (Opposite.op j)
      calc
        _ = V.map f.op ≫ η.app (Opposite.op i) := congrArg (fun g => V.map f.op ≫ g)
          (Category.comp_id (η.app (Opposite.op i)))
        _ = η.app (Opposite.op j) := (η.naturality f.op).trans (Category.comp_id _))
  exact hx.trans h

lemma nerveUnderLift_rightOp_native_pairing {I C : Type u} [Category.{u} I] [Category.{u} C]
    {c : C} {V : Iᵒᵖ ⥤ C} (η : V ⟶ (Functor.const Iᵒᵖ).obj c) {D : SSet.{u}}
    (F : nerve C ⟶ D) :
    let Fop := (nerveOppositeIso (C := C)).inv ≫ SSet.opFunctor.map F
    nerveMap (Under.lift (X := Opposite.op c) V.rightOp (NatTrans.rightOp η)) ≫
      nerveUnderMap (Opposite.op c) ≫ sliceUnderPostcomp (nervePoint (Opposite.op c)) Fop ≫
        cosliceOppositeTwistedArrowMap (nervePoint (Opposite.op c) ≫ Fop) =
      twistedPairingNerveMap V.rightOp ((Functor.const I).obj c)
        (fun i => η.app (Opposite.op i)) (by
          intro i j f
          change V.map f.op ≫ η.app (Opposite.op i) ≫ 𝟙 c = η.app (Opposite.op j)
          calc
            _ = V.map f.op ≫ η.app (Opposite.op i) := congrArg (fun g => V.map f.op ≫ g)
              (Category.comp_id (η.app (Opposite.op i)))
            _ = η.app (Opposite.op j) := (η.naturality f.op).trans (Category.comp_id _)) ≫
        edgewiseSubdivisionMap F := by
  dsimp only
  let Fop := (nerveOppositeIso (C := C)).inv ≫ SSet.opFunctor.map F
  have hb := nerveUnderLift_comp_cosliceTwistedArrowMap (c := Opposite.op c)
    (V := V.rightOp) (NatTrans.rightOp η)
  have hL := nerveUnderLift_comp_cosliceTwistedArrowMap_postcomp (c := Opposite.op c)
    (V := V.rightOp) (NatTrans.rightOp η) Fop
  have hL' := congrArg (fun f : nerve I ⟶ TwistedArrow D.op =>
    f ≫ twistedArrowOppositeSwap D) hL
  rw [← hb] at hL'
  have hm : edgewiseSubdivisionMap Fop =
      edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
        edgewiseSubdivisionMap (SSet.opFunctor.map F) :=
    edgewiseSubdivisionFunctor.map_comp _ _
  rw [hm] at hL'
  simp only [Category.assoc] at hL'
  rw [twistedArrowOppositeSwap_naturality F] at hL'
  have hR := congrArg (fun f : nerve I ⟶ TwistedArrow (nerve C) =>
    f ≫ edgewiseSubdivisionMap F) (nerveUnderLift_rightOp_pairing η)
  simp only [Category.assoc] at hR
  have h := hL'.trans hR
  simpa only [cosliceOppositeTwistedArrowMap, Category.assoc] using h
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
end

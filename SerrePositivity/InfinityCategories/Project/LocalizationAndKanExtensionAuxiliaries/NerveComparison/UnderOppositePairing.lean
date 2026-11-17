module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderLiftTwistedPairing
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedPairingOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceTwistedArrowTargetNaturality

/-! 固定標的の同じ全pairingの反対coslice表示と、指定モデル源での像の照合。 -/

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

/-- 元の固定標的の自然変換の全pairingを、同じ反対cosliceから回収する。 -/
lemma nerveUnderLift_opposite_pairing {I C : Type u} [Category.{u} I] [Category.{u} C]
    {c : C} {V : I ⥤ C} (η : V ⟶ (Functor.const I).obj c) :
    nerveMap (Under.lift (X := Opposite.op c) V.op (NatTrans.op η)) ≫ nerveUnderMap (Opposite.op c) ≫
      cosliceTwistedArrowMap (nervePoint (Opposite.op c)) ≫
        edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
          twistedArrowOppositeSwap (nerve C) =
      twistedPairingNerveMap V.op ((Functor.const Iᵒᵖ).obj c)
        (fun i => η.app i.unop) (by
          intro i j f
          change V.map f.unop ≫ η.app i.unop ≫ 𝟙 c = η.app j.unop
          calc
            _ = V.map f.unop ≫ η.app i.unop := congrArg (fun g => V.map f.unop ≫ g)
              (Category.comp_id (η.app i.unop))
            _ = η.app j.unop := (η.naturality f.unop).trans (Category.comp_id _)) := by
  have hp := nerveUnderLift_comp_cosliceTwistedArrowMap (c := Opposite.op c)
    (V := V.op) (NatTrans.op η)
  have hx := congrArg (fun f : nerve Iᵒᵖ ⟶ TwistedArrow (nerve Cᵒᵖ) =>
    f ≫ edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
      twistedArrowOppositeSwap (nerve C)) hp
  have h := twistedPairingNerveMap_opposite_swap V.op ((Functor.const Iᵒᵖ).obj c)
    (fun i => η.app i.unop) (by
      intro i j f
      change V.map f.unop ≫ η.app i.unop ≫ 𝟙 c = η.app j.unop
      calc
        _ = V.map f.unop ≫ η.app i.unop := congrArg (fun g => V.map f.unop ≫ g)
          (Category.comp_id (η.app i.unop))
        _ = η.app j.unop := (η.naturality f.unop).trans (Category.comp_id _))
  exact hx.trans h

/-- 同じ固定標的の族は、指定モデル源で送った元のnative pairingを厳密に回収する。 -/
lemma nerveUnderLift_opposite_native_pairing {I C : Type u} [Category.{u} I] [Category.{u} C]
    {c : C} {V : I ⥤ C} (η : V ⟶ (Functor.const I).obj c) {D : SSet.{u}}
    (F : nerve C ⟶ D) :
    let Fop := (nerveOppositeIso (C := C)).inv ≫ SSet.opFunctor.map F
    nerveMap (Under.lift (X := Opposite.op c) V.op (NatTrans.op η)) ≫
      nerveUnderMap (Opposite.op c) ≫ sliceUnderPostcomp (nervePoint (Opposite.op c)) Fop ≫
        cosliceOppositeTwistedArrowMap (nervePoint (Opposite.op c) ≫ Fop) =
      twistedPairingNerveMap V.op ((Functor.const Iᵒᵖ).obj c)
        (fun i => η.app i.unop) (by
          intro i j f
          change V.map f.unop ≫ η.app i.unop ≫ 𝟙 c = η.app j.unop
          calc
            _ = V.map f.unop ≫ η.app i.unop := congrArg (fun g => V.map f.unop ≫ g)
              (Category.comp_id (η.app i.unop))
            _ = η.app j.unop := (η.naturality f.unop).trans (Category.comp_id _)) ≫
        edgewiseSubdivisionMap F := by
  dsimp only
  let Fop := (nerveOppositeIso (C := C)).inv ≫ SSet.opFunctor.map F
  have hb := nerveUnderLift_comp_cosliceTwistedArrowMap (c := Opposite.op c)
    (V := V.op) (NatTrans.op η)
  have hL := nerveUnderLift_comp_cosliceTwistedArrowMap_postcomp (c := Opposite.op c)
    (V := V.op) (NatTrans.op η) Fop
  have hL' := congrArg (fun f : nerve Iᵒᵖ ⟶ TwistedArrow D.op =>
    f ≫ twistedArrowOppositeSwap D) hL
  rw [← hb] at hL'
  have hm : edgewiseSubdivisionMap Fop =
      edgewiseSubdivisionMap (nerveOppositeIso (C := C)).inv ≫
        edgewiseSubdivisionMap (SSet.opFunctor.map F) :=
    edgewiseSubdivisionFunctor.map_comp _ _
  rw [hm] at hL'
  simp only [Category.assoc] at hL'
  rw [twistedArrowOppositeSwap_naturality F] at hL'
  have hR := congrArg (fun f : nerve Iᵒᵖ ⟶ TwistedArrow (nerve C) =>
    f ≫ edgewiseSubdivisionMap F) (nerveUnderLift_opposite_pairing η)
  simp only [Category.assoc] at hR
  have h := hL'.trans hR
  simpa only [cosliceOppositeTwistedArrowMap, Category.assoc] using h
end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
end

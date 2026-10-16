module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.HomotopyEndpointComparison
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-! # Homotopy extension into a Kan complex along an anodyne extension -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.KanHomotopyExtension
variable {A B K : SSet.{v}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include hi hK in
lemma exists_extension (f : A ⟶ K) : ∃ g : B ⟶ K, i ≫ g = f := by
  have : HasLiftingProperty i (terminal.from K) := hi _ hK
  let sq : CommSq f i (terminal.from K) (terminal.from B) := ⟨by simp⟩
  exact ⟨sq.lift, sq.fac_left⟩

lemma boundary_compatibility (f g : B ⟶ K) (H : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    i ▷ (SSet.boundary 1).toSSet ≫ LargeParameterHomotopy.boundaryMap f g =
      A ◁ (SSet.boundary 1).ι ≫ H.h := by
  apply (LargeParameterHomotopy.boundaryColimit A).hom_ext
  rintro ⟨j⟩
  cases j
  · change (A ◁ SSet.boundary.ι (1 : Fin 2)) ≫ _ =
      (A ◁ SSet.boundary.ι (1 : Fin 2)) ≫ _
    rw [← Category.assoc, whisker_exchange, Category.assoc,
      LargeParameterHomotopy.boundaryMap_zero]
    conv_rhs => rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      HomotopyEndpointComparison.face_zero]
    exact whiskerRight_fst_assoc i _ f
  · change (A ◁ SSet.boundary.ι (0 : Fin 2)) ≫ _ =
      (A ◁ SSet.boundary.ι (0 : Fin 2)) ≫ _
    rw [← Category.assoc, whisker_exchange, Category.assoc,
      LargeParameterHomotopy.boundaryMap_one]
    conv_rhs => rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      HomotopyEndpointComparison.face_one]
    exact whiskerRight_fst_assoc i _ g

include hi hK in
lemma exists_homotopy (f g : B ⟶ K) (H : SSet.Homotopy (i ≫ f) (i ≫ g)) :
    Nonempty (SSet.Homotopy f g) := by
  let pp := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{v}) i
    (SSet.boundary 1).ι
  have ha : SSet.anodyneExtensions pp.ι := SSet.anodyneExtensions_pushoutObjObjι' pp hi
  have : HasLiftingProperty pp.ι (terminal.from K) := ha _ hK
  let b := pp.isPushout.desc (LargeParameterHomotopy.boundaryMap f g) H.h
    (boundary_compatibility i f g H)
  let sq : CommSq b pp.ι (terminal.from K) (terminal.from _) := ⟨by simp⟩
  have hb : B ◁ (SSet.boundary 1).ι ≫ sq.lift =
      LargeParameterHomotopy.boundaryMap f g := by
    rw [show B ◁ (SSet.boundary 1).ι = pp.inl ≫ pp.ι from pp.inl_ι.symm,
      Category.assoc, sq.fac_left]
    exact pp.isPushout.inl_desc _ _ _
  refine ⟨{ h := sq.lift, h₀ := ?_, h₁ := ?_, rel := ?_ }⟩
  · change SSet.ι₀ ≫ sq.lift = f
    rw [← LargeParameterHomotopy.section_zero B, Category.assoc,
      ← SSet.boundary.ι_ι (1 : Fin 2), whiskerLeft_comp, Category.assoc, hb,
      LargeParameterHomotopy.boundaryMap_zero]
    rfl
  · change SSet.ι₁ ≫ sq.lift = g
    rw [← LargeParameterHomotopy.section_one B, Category.assoc,
      ← SSet.boundary.ι_ι (0 : Fin 2), whiskerLeft_comp, Category.assoc, hb,
      LargeParameterHomotopy.boundaryMap_one]
    rfl
  · apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

end SerrePositivity.SimplicialModel.KanHomotopyExtension

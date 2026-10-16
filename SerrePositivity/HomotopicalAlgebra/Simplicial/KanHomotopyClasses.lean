module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyExtension

/-! # Kan valued homotopy classes invert every anodyne extension

An inverse is constructed by extension. Homotopy extension proves that this
construction descends to classes and is independent of the selected extensions.
-/

@[expose] public section
universe v
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

namespace SerrePositivity.SimplicialModel.KanHomotopyClasses
open HomotopyClasses
variable {A B K : SSet.{v}} (i : A ⟶ B) (hi : SSet.anodyneExtensions i)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

def extension (f : A ⟶ K) : B ⟶ K :=
  (KanHomotopyExtension.exists_extension i hi hK f).choose

@[simp] lemma extension_fac (f : A ⟶ K) : i ≫ extension i hi hK f = f :=
  (KanHomotopyExtension.exists_extension i hi hK f).choose_spec

def inverse : obj A K → obj B K :=
  Quot.lift (fun f => mk (extension i hi hK f)) (by
    intro f g h
    obtain ⟨H⟩ := h
    apply Quot.sound
    apply KanHomotopyExtension.exists_homotopy i hi hK
    simpa only [extension_fac] using H)

lemma inverse_right (x : obj A K) : pre i (inverse i hi hK x) = x := by
  refine Quot.inductionOn x (fun f => ?_)
  exact congrArg mk (extension_fac i hi hK f)

lemma inverse_left (x : obj B K) : inverse i hi hK (pre i x) = x := by
  refine Quot.inductionOn x (fun f => ?_)
  apply Quot.sound
  apply KanHomotopyExtension.exists_homotopy i hi hK
  rw [extension_fac]
  exact SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (i ≫ f))

include hi hK in
lemma pre_bijective : Function.Bijective (pre i (K := K)) :=
  ⟨Function.LeftInverse.injective (inverse_left i hi hK),
    Function.RightInverse.surjective (inverse_right i hi hK)⟩

lemma functor_inverts (K : SSet.{v})
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    SSet.anodyneExtensions.op.IsInvertedBy (functor K) := by
  intro X Y f hf
  exact (isIso_iff_bijective _).mpr (pre_bijective f.unop hf hK)

lemma rightOp_inverts (K : SSet.{v})
    (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K)) :
    SSet.anodyneExtensions.IsInvertedBy (functor K).rightOp :=
  (functor_inverts K hK).rightOp

end SerrePositivity.SimplicialModel.KanHomotopyClasses

module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.PiZeroConstant
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanTestDetection

/-! # Anodyne-localized equivalences induce bijections on actual components

Discrete Kan tests identify precomposition on homotopy classes with
precomposition on functions out of components. No model structure is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.PiZeroLocalization
open PiZeroConstant
variable {X Y : SSet.{v}} {T : Type v}

def classEquiv : HomotopyClasses.obj X (discrete T) ≃ (SSet.π₀ X → T) where
  toFun := Quot.lift toComponents (fun _ _ ⟨H⟩ => congrArg toComponents (homotopy_eq H))
  invFun t := HomotopyClasses.mk (fromComponents t)
  left_inv z := by
    refine Quot.inductionOn z (fun f => ?_)
    exact congrArg HomotopyClasses.mk (homEquiv.left_inv f)
  right_inv t := homEquiv.right_inv t

lemma classEquiv_pre (f : X ⟶ Y) (z : HomotopyClasses.obj Y (discrete T)) :
    classEquiv (HomotopyClasses.pre f z) = classEquiv z ∘ SSet.mapπ₀ f := by
  refine Quot.inductionOn z (fun g => ?_)
  funext c
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective c
  rfl

lemma precomposition_bijective (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) (T : Type v) :
    Function.Bijective (fun t : SSet.π₀ Y → T => t ∘ SSet.mapπ₀ f) := by
  let eX := classEquiv (X := X) (T := T)
  let eY := classEquiv (X := Y) (T := T)
  have he : (fun t : SSet.π₀ Y → T => t ∘ SSet.mapπ₀ f) =
      fun t => eX (HomotopyClasses.pre f (eY.symm t)) := by
    funext t
    rw [classEquiv_pre]
    exact congrArg (· ∘ SSet.mapπ₀ f) (eY.apply_symm_apply t).symm
  rw [he]
  exact eX.bijective.comp
    ((KanTestDetection.tests_of_anodyneQ_isIso f hf _ (discrete_terminal_rlp T)).comp
      eY.symm.bijective)

lemma bijective_of_precomposition {A B : Type v} (p : A → B)
    (hs : Function.Surjective (fun t : B → A => t ∘ p))
    (hi : Function.Injective (fun t : B → B => t ∘ p)) : Function.Bijective p := by
  obtain ⟨l, hl⟩ := hs id
  have hr : p ∘ l = id := hi (by
    funext a
    exact congrArg p (congrFun hl a))
  refine ⟨fun a b hab => ?_, fun b => ⟨l b, congrFun hr b⟩⟩
  calc
    a = l (p a) := (congrFun hl a).symm
    _ = l (p b) := congrArg l hab
    _ = b := congrFun hl b

lemma piZero_bijective (f : X ⟶ Y)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) :
    Function.Bijective (SSet.mapπ₀ f) :=
  bijective_of_precomposition _
    (precomposition_bijective f hf (SSet.π₀ X)).surjective
    (precomposition_bijective f hf (SSet.π₀ Y)).injective

lemma inverts_anodyne : SSet.anodyneExtensions.IsInvertedBy SSet.π₀Functor.{v} := by
  intro X Y f hf
  exact (CategoryTheory.isIso_iff_bijective _).mpr
    (piZero_bijective f (Localization.inverts AnodyneHomotopy.anodyneQ _ f hf))

end SerrePositivity.SimplicialModel.PiZeroLocalization

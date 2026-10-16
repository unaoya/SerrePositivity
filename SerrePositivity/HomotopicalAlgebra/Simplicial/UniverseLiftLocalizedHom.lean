module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanLocalizedRepresentatives
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftAnodyneReflection

/-! # Small homotopy classes compute localized Hom between lifted small Kan values

This controls Hom size after localization. It does not shrink the simplices
of the original large space or construct a strict small replacement diagram.
-/

@[expose] public section
universe w v uD vD
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.UniverseLift
variable {D : Type uD} [Category.{vD} D] (L : SSet.{max w v} ⥤ D)
  [L.IsLocalization SSet.anodyneExtensions]
  (X K : SSet.{v}) (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

/-- The small source of the equivalence is the original homotopy-class type. -/
def smallLocalizedHomEquiv : HomotopyClasses.obj X K ≃
    (L.obj (obj.{w} X) ⟶ L.obj (obj.{w} K)) :=
  (homotopyClassEquiv.{w} X K).trans
    (KanLocalizedRepresentatives.homEquiv L (horn_terminal_map hK) (obj X))

@[simp] lemma smallLocalizedHomEquiv_mk (f : X ⟶ K) :
    smallLocalizedHomEquiv L X K hK (HomotopyClasses.mk f) = L.map (map.{w} f) := rfl

include hK in
lemma small_localizedHom : Small.{v} (L.obj (obj.{w} X) ⟶ L.obj (obj.{w} K)) :=
  small_map (smallLocalizedHomEquiv L X K hK).symm

/-- Every localized arrow between lifted small values has an original small
map as representative. The target is Kan in the original small universe. -/
def localizedRepresentative (φ : L.obj (obj.{w} X) ⟶ L.obj (obj.{w} K)) : X ⟶ K :=
  (Quot.exists_rep ((smallLocalizedHomEquiv L X K hK).symm φ)).choose

lemma localizedRepresentative_map (φ : L.obj (obj.{w} X) ⟶ L.obj (obj.{w} K)) :
    L.map (map.{w} (localizedRepresentative L X K hK φ)) = φ := by
  change smallLocalizedHomEquiv L X K hK
    (HomotopyClasses.mk (localizedRepresentative L X K hK φ)) = φ
  exact (congrArg (smallLocalizedHomEquiv L X K hK)
    (Quot.exists_rep ((smallLocalizedHomEquiv L X K hK).symm φ)).choose_spec).trans
      ((smallLocalizedHomEquiv L X K hK).apply_symm_apply φ)

include hK in
lemma localized_map_eq_iff_homotopy (f g : X ⟶ K) :
    L.map (map.{w} f) = L.map (map.{w} g) ↔ Nonempty (SSet.Homotopy f g) :=
  ⟨fun he => KanActualHomotopy.of_class_eq hK
      ((smallLocalizedHomEquiv L X K hK).injective he),
    fun ⟨H⟩ => AnodyneHomotopy.map_homotopy_eq L (Localization.inverts L _) (homotopy H)⟩

end SerrePositivity.SimplicialModel.UniverseLift

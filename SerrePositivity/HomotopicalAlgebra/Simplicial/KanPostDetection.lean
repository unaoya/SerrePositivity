module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanActualHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-! # Two postcomposition tests detect localized equivalences between Kan objects -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanPostDetection
variable {X Y : SSet.{v}} (f : X ⟶ Y)
  (hX : SSet.modelCategoryQuillen.J.rlp (terminal.from X))
  (hY : SSet.modelCategoryQuillen.J.rlp (terminal.from Y))

include hX hY in
lemma localized_isIso
    (hs : Function.Surjective (HomotopyClasses.post f (X := Y)))
    (hi : Function.Injective (HomotopyClasses.post f (X := X))) :
    IsIso (AnodyneHomotopy.anodyneQ.map f) := by
  obtain ⟨r, hr⟩ := hs (HomotopyClasses.mk (𝟙 Y))
  obtain ⟨g, rfl⟩ := Quot.exists_rep r
  have hgf : HomotopyClasses.mk (g ≫ f) = HomotopyClasses.mk (𝟙 Y) := hr
  have hfg : HomotopyClasses.mk (f ≫ g) = HomotopyClasses.mk (𝟙 X) := hi (by
    change HomotopyClasses.mk ((f ≫ g) ≫ f) = HomotopyClasses.mk (𝟙 X ≫ f)
    rw [Category.assoc, Category.id_comp]
    have h := congrArg (HomotopyClasses.pre f) hgf
    simpa only [HomotopyClasses.pre_mk, Category.comp_id] using h)
  obtain ⟨Hfg⟩ := KanActualHomotopy.of_class_eq hX hfg
  obtain ⟨Hgf⟩ := KanActualHomotopy.of_class_eq hY hgf
  let Q := AnodyneHomotopy.anodyneQ.{v}
  have hQ := Localization.inverts Q SSet.anodyneExtensions
  exact ⟨⟨Q.map g,
    (Q.map_comp _ _).symm.trans
      ((AnodyneHomotopy.map_homotopy_eq Q hQ Hfg).trans (Q.map_id _)),
    (Q.map_comp _ _).symm.trans
      ((AnodyneHomotopy.map_homotopy_eq Q hQ Hgf).trans (Q.map_id _))⟩⟩

end SerrePositivity.SimplicialModel.KanPostDetection

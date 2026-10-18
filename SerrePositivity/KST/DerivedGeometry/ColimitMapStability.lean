module

public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
概要：射の性質の余極限での安定性を選ばれた colimMap で判定する。
方針：任意の余錐を選ばれた余極限と同型で比較する。
規約：射の性質は同型で不変。
使われ方：Stacks 19.12.6、TT §3・§8、Toën §3.2 の超限工程での準同型性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {J C : Type*} [Category* J] [Category* C] [HasColimitsOfShape J C]

/--
概要：選ばれた colimMap に対する閉性は任意の J 型余極限に対する閉性を与える。
方針：両側の余極限の一意同型で射を比較する。
規約：同型不変な射の性質。
使われ方：Stacks Theorem 19.12.6、TT §3 の極限順序数での射の性質。
-/
lemma stableUnderColimits_of_colimMap (W : MorphismProperty C) [W.RespectsIso]
    (h : ∀ {F G : J ⥤ C} (f : F ⟶ G), W.functorCategory J f → W (colim.map f)) :
    W.IsStableUnderColimitsOfShape J where
  condition F G c₁ c₂ h₁ h₂ f hf φ hφ := by
    let e₁ := h₁.coconePointUniqueUpToIso (colimit.isColimit F)
    let e₂ := h₂.coconePointUniqueUpToIso (colimit.isColimit G)
    have hw : e₁.hom ≫ colim.map f = φ ≫ e₂.hom := by
      apply h₁.hom_ext
      intro j
      calc
        c₁.ι.app j ≫ e₁.hom ≫ colim.map f = colimit.ι F j ≫ colim.map f := by
          rw [← Category.assoc, h₁.comp_coconePointUniqueUpToIso_hom (colimit.isColimit F) j]
          rfl
        _ = f.app j ≫ colimit.ι G j := ι_colimMap f j
        _ = f.app j ≫ c₂.ι.app j ≫ e₂.hom := by
          exact congrArg (fun x => f.app j ≫ x)
            (h₂.comp_coconePointUniqueUpToIso_hom (colimit.isColimit G) j).symm
        _ = c₁.ι.app j ≫ φ ≫ e₂.hom := by
          simpa only [Category.assoc] using congrArg (fun x => x ≫ e₂.hom) (hφ j).symm
    let e : Arrow.mk φ ≅ Arrow.mk (colim.map f) := Arrow.isoMk e₁ e₂ hw
    exact (W.arrow_iso_iff e).mpr (h f hf)

end SerrePositivity.KST.DerivedGeometry

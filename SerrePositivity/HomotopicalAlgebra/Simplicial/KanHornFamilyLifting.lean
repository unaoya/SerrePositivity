module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterizedHornChoices

/-! # Lift varying horn families while retaining prescribed earlier whole fillers

A section of the simplicial restriction map gives one uniform filling
operation natural in every parameter. Relative lifting also permits the
specified horn family to vary, while retaining the earlier entire filler
on a parameter subcomplex. No model structure is used.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.KanHornFamilyLifting
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (CategoryTheory.Limits.terminal.from K))

abbrev restriction :
    (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K ⟶
      (ihom (SSet.horn (n + 1) i).toSSet).obj K :=
  (pre (SSet.horn (n + 1) i).ι).app K

abbrev section_ := LocalizedRelativeChoice.restrictionSection (SSet.horn (n + 1) i).ι
  ParameterizedHornChoices.horn_localized_isIso hK

lemma section_fac : section_ K i hK ≫ restriction K i = 𝟙 _ :=
  LocalizedRelativeChoice.restrictionSection_fac _ _ _

variable {L : SSet.{v}} (b : L ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)

abbrev uniform : L ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K :=
  b ≫ section_ K i hK

lemma uniform_restriction : uniform K i hK b ≫ restriction K i = b := by
  rw [uniform, Category.assoc, section_fac, Category.comp_id]

lemma uniform_naturality {U : SSet.{v}} (j : U ⟶ L) :
    uniform K i hK (j ≫ b) = j ≫ uniform K i hK b := Category.assoc _ _ _

abbrev uniformFamily : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⊗ L ⟶ K :=
  uncurry (uniform K i hK b)

lemma uniformFamily_boundary :
    (SSet.horn (n + 1) i).ι ▷ L ≫ uniformFamily K i hK b = uncurry b :=
  (uncurry_pre_app K (uniform K i hK b) (SSet.horn (n + 1) i).ι).symm.trans
    (congrArg uncurry (uniform_restriction K i hK b))

lemma uniformFamily_naturality {U : SSet.{v}} (j : U ⟶ L) :
    uniformFamily K i hK (j ≫ b) = SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ j ≫
      uniformFamily K i hK b := by
  rw [uniformFamily, uniform_naturality, uncurry_natural_left]

variable {U V : SSet.{v}} (j : U ⟶ V) [Mono j]
  (boundary : V ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)
  (earlier : U ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K)
  (hearlier : earlier ≫ restriction K i = j ≫ boundary)

include hK in
lemma all_mono_rlp : (MorphismProperty.monomorphisms SSet.{v}).rlp (restriction K i) :=
  KanRestrictionLifting.all_mono_rlp _ ParameterizedHornChoices.horn_localized_isIso hK

def relativeLift :
    { e : V ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K //
      j ≫ e = earlier ∧ e ≫ restriction K i = boundary } := by
  have : HasLiftingProperty j (restriction K i) := all_mono_rlp K i hK j inferInstance
  let sq : CommSq earlier j (restriction K i) boundary := ⟨hearlier⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

abbrev relativeFamily : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⊗ V ⟶ K :=
  uncurry (relativeLift K i hK j boundary earlier hearlier).val

lemma relativeFamily_earlier : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ j ≫
    relativeFamily K i hK j boundary earlier hearlier = uncurry earlier := by
  change _ ≫ uncurry _ = _
  rw [← uncurry_natural_left, (relativeLift K i hK j boundary earlier hearlier).property.1]

lemma relativeFamily_boundary : (SSet.horn (n + 1) i).ι ▷ V ≫
    relativeFamily K i hK j boundary earlier hearlier = uncurry boundary :=
  (uncurry_pre_app K (relativeLift K i hK j boundary earlier hearlier).val
    (SSet.horn (n + 1) i).ι).symm.trans
      (congrArg uncurry (relativeLift K i hK j boundary earlier hearlier).property.2)

end SerrePositivity.SimplicialModel.KanHornFamilyLifting

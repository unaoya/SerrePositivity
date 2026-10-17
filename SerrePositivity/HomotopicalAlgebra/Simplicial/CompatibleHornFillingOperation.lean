module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.CompatibleInputUnion
public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeHornFillingOperation

/-! # One filling operation retains arbitrarily many compatible prescribed families

The index universe is independent of the simplicial value universe.
Individual family maps need not be monomorphisms. Their agreement on
coincident inputs makes them descend to a small union; the union's
inclusion is the monomorphism used for relative horn lifting.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.CompatibleHornFillingOperation
variable (K : SSet.{v}) {n : ℕ} (i : Fin (n + 2))
  (hK : SSet.modelCategoryQuillen.J.rlp (CategoryTheory.Limits.terminal.from K))
  {J : Type u} (S : J → SSet.{v})
  (b : ∀ j, S j ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)
  (a : ∀ j, S j ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K)
  (h : CompatibleInputUnion.Compatible S b a)
  (ha : ∀ j, a j ≫ KanHornFamilyLifting.restriction K i = b j)

abbrev inputs := CompatibleInputUnion.inputs S b

abbrev section_ := RelativeHornFillingOperation.section_ K i hK (inputs K i S b).ι
  (CompatibleInputUnion.lift S b a h)
  (CompatibleInputUnion.lift_over S b a h (KanHornFamilyLifting.restriction K i) ha)

lemma section_restriction : section_ K i hK S b a h ha ≫
    KanHornFamilyLifting.restriction K i = 𝟙 _ :=
  RelativeHornFillingOperation.section_restriction _ _ _ _ _ _

lemma section_prescribed (j : J) : b j ≫ section_ K i hK S b a h ha = a j := by
  calc
    _ = (CompatibleInputUnion.toInputs S b j ≫ (inputs K i S b).ι) ≫
        section_ K i hK S b a h ha := by rw [CompatibleInputUnion.toInputs_inclusion]
    _ = CompatibleInputUnion.toInputs S b j ≫ CompatibleInputUnion.lift S b a h := by
      rw [Category.assoc, RelativeHornFillingOperation.section_prescribed]
    _ = _ := CompatibleInputUnion.toInputs_lift S b a h j

variable {L : SSet.{v}} (boundary : L ⟶ (ihom (SSet.horn (n + 1) i).toSSet).obj K)

abbrev fill : L ⟶ (ihom (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).obj K :=
  boundary ≫ section_ K i hK S b a h ha

lemma fill_restriction : fill K i hK S b a h ha boundary ≫
    KanHornFamilyLifting.restriction K i = boundary := by
  rw [fill, Category.assoc, section_restriction, Category.comp_id]

lemma fill_naturality {U : SSet.{v}} (j : U ⟶ L) :
    fill K i hK S b a h ha (j ≫ boundary) = j ≫ fill K i hK S b a h ha boundary :=
  Category.assoc _ _ _

lemma fill_prescribed (j : J) {U : SSet.{v}} (q : U ⟶ S j) :
    fill K i hK S b a h ha (q ≫ b j) = q ≫ a j := by
  rw [fill, Category.assoc, section_prescribed]

lemma family_prescribed (j : J) {U : SSet.{v}} (q : U ⟶ S j) :
    uncurry (fill K i hK S b a h ha (q ≫ b j)) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ q ≫ uncurry (a j) := by
  rw [fill_prescribed, uncurry_natural_left]

end SerrePositivity.SimplicialModel.CompatibleHornFillingOperation

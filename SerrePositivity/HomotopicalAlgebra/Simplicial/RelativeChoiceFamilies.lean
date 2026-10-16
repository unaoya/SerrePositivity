module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceSpace
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterComposition

/-! # The universal property of actual relative extension families

Families with their entire fixed boundary are exactly maps to the
pullback choice space. No model structure or Kan condition is needed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.RelativeChoiceSpace
variable {A B K T U : SSet.{v}} (i : A ⟶ B) (b : A ⟶ K)

lemma family_boundary_const (s : T ⟶ obj i b) :
    i ▷ T ≫ family i b s = ParameterComposition.const T b := by
  rw [family_fixed_boundary]
  ext n x
  rfl

lemma family_ofExtension_const (e : B ⟶ K) (he : i ≫ e = b) :
    family i b (ofExtension i b e he) =
      ParameterComposition.const (SSet.stdSimplex.obj (SimplexCategory.mk 0)) e := by
  rw [family_ofExtension]
  ext n x
  rfl

lemma uncurry_constant_name :
    uncurry (SSet.stdSimplex.isTerminalObj₀.from T ≫ name b) =
      ParameterComposition.const T b := by
  rw [name, ← Category.assoc, uncurry_natural_left]
  dsimp only [curry']
  rw [uncurry_curry]
  ext n x
  rfl

def ofFamily (h : B ⊗ T ⟶ K) (hh : i ▷ T ≫ h = ParameterComposition.const T b) :
    T ⟶ obj i b :=
  pullback.lift (curry h) (SSet.stdSimplex.isTerminalObj₀.from T) (by
    apply uncurry_injective
    change uncurry (curry h ≫ (pre i).app K) = _
    rw [uncurry_pre_app, uncurry_curry, hh, uncurry_constant_name])

lemma ofFamily_family (h : B ⊗ T ⟶ K)
    (hh : i ▷ T ≫ h = ParameterComposition.const T b) :
    family i b (ofFamily i b h hh) = h := by
  rw [family, ofFamily, pullback.lift_fst, uncurry_curry]

lemma family_injective : Function.Injective (family i b (K := T)) := by
  intro s t h
  apply pullback.hom_ext
  · exact uncurry_injective h
  · exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _

lemma family_ofFamily (s : T ⟶ obj i b) :
    ofFamily i b (family i b s) (family_boundary_const i b s) = s := by
  apply family_injective i b
  exact ofFamily_family i b _ _

def familyEquiv : (T ⟶ obj i b) ≃
    {h : B ⊗ T ⟶ K // i ▷ T ≫ h = ParameterComposition.const T b} where
  toFun s := ⟨family i b s, family_boundary_const i b s⟩
  invFun h := ofFamily i b h.1 h.2
  left_inv := family_ofFamily i b
  right_inv h := Subtype.ext (ofFamily_family i b h.1 h.2)

lemma ofFamily_naturality (j : U ⟶ T) (h : B ⊗ T ⟶ K)
    (hh : i ▷ T ≫ h = ParameterComposition.const T b)
    (hj : i ▷ U ≫ (B ◁ j ≫ h) = ParameterComposition.const U b) :
    j ≫ ofFamily i b h hh = ofFamily i b (B ◁ j ≫ h) hj := by
  apply family_injective i b
  rw [family_naturality, ofFamily_family, ofFamily_family]

end SerrePositivity.SimplicialModel.RelativeChoiceSpace

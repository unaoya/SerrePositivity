module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessBaseChange
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSourceChange
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessMapOver
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativePathCompositionCongr

/-!
概要：底変更した元の class 経路に、元の標的側の後続経路を接合する。
方針：全経路の像の一致から接合端点を回収し、実 pullback の一意性で lift を揃える。
規約：元の経路の全射を保持。使われ方：fixed 模型射への自然性と W の接合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B W : Mon (Complex R)}
  (q : A ⟶ B) (N : Bimod B B) (a : W ⟶ A)
  {x b : W ⟶ algebra A (bimoduleRestrict q N)}
  {x₀ y₀ z₀ : W ⟶ algebra B N}
  (v : RelativeWitness a (bimoduleRestrict q N) x b)
  (v₀ : RelativeWitness (a ≫ q) N x₀ y₀)
  (hv : v.hom ≫ DGAlgebra.Path.map R (baseChangeMap q N) = v₀.hom)
  (w : RelativeWitness (a ≫ q) N y₀ z₀)

include hv in
lemma baseChangeFollowing_target : b ≫ baseChangeMap q N = y₀ := by
  rw [← v.target_eq, Category.assoc, ← DGAlgebra.Path.map_target,
    ← Category.assoc, hv, v₀.target_eq]

include hv in
lemma baseChangeFollowing_source : baseChangeLift q N a y₀ w.source_projection = b := by
  apply baseChange_hom_ext q N
  · exact (baseChangeLift_projection q N a y₀ w.source_projection).trans
      v.target_projection.symm
  · exact (baseChangeLift_map q N a y₀ w.source_projection).trans
      (baseChangeFollowing_target q N a v v₀ hv).symm

def baseChangeFollowingWitness : RelativeWitness a (bimoduleRestrict q N) b
    (baseChangeLift q N a z₀ w.target_projection) :=
  (baseChangeRelativeWitness q N a w).changeSource
    (baseChangeFollowing_source q N a v v₀ hv w)

lemma baseChangeFollowingWitness_hom : (baseChangeFollowingWitness q N a v v₀ hv w).hom =
    (baseChangeRelativeWitness q N a w).hom :=
  RelativeWitness.changeSource_hom _ _

lemma baseChangeFollowingWitness_map : (baseChangeFollowingWitness q N a v v₀ hv w).hom ≫
    DGAlgebra.Path.map R (baseChangeMap q N) = w.hom := by
  rw [baseChangeFollowingWitness_hom, baseChangeRelativeWitness_map]

lemma baseChangeFollowingWitness_comp_map :
    (v.comp (baseChangeFollowingWitness q N a v v₀ hv w)).hom ≫
      DGAlgebra.Path.map R (baseChangeMap q N) = (v₀.comp w).hom := by
  let t := baseChangeFollowingWitness q N a v v₀ hv w
  let h := RelativeWitness.mapOver_comp_hom q (baseChangeMap q N)
    (baseChangeMap_projection q N) v t
  let k := RelativeWitness.comp_congr_hom_of_paths
    (v := v.mapOver q (baseChangeMap q N) (baseChangeMap_projection q N))
    (w := t.mapOver q (baseChangeMap q N) (baseChangeMap_projection q N))
    (v' := v₀) (w' := w) hv (baseChangeFollowingWitness_map q N a v v₀ hv w)
  exact h.trans k

end SerrePositivity.KST.LocalizingInvariants.SquareZero

module

public import SerrePositivity.KST.LocalizingInvariants.CochainKernelHomology
public import SerrePositivity.KST.LocalizingInvariants.CochainConeMapQuasiIso
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
概要：実複体の二つの準同型は、その直和の元の対角射でも準同型を与える。
方針：各ホモロジー関手の実直和比較と、その対角射への自然性を使う。
規約：非有界複体に適用。使われ方：homotopy pullback の一脚の準同型置換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable {R : Type u} [CommRing R] {K K' L L' : Complex R}

lemma cochainBiprodMap_quasiIso (a : K ⟶ K') (b : L ⟶ L') (ha : QuasiIso a) (hb : QuasiIso b) :
    QuasiIso (biprod.map a b) := by
  have := ha
  have := hb
  rw [quasiIso_iff]
  intro j
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℤ) j
  have : F.Additive := by dsimp [F]; infer_instance
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  change IsIso (F.map (biprod.map a b))
  have : IsIso (F.map a) := by change IsIso (homologyMap a j); infer_instance
  have : IsIso (F.map b) := by change IsIso (homologyMap b j); infer_instance
  have hn : F.map (biprod.map a b) ≫ (F.mapBiprod K' L').hom =
      (F.mapBiprod K L).hom ≫ biprod.map (F.map a) (F.map b) := by
    apply biprod.hom_ext
    · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_fst, biprod.map_fst,
        ← F.map_comp, biprod.map_fst]
      rw [biprod.lift_fst_assoc, ← F.map_comp]
    · simp only [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd, biprod.map_snd,
        ← F.map_comp, biprod.map_snd]
      rw [biprod.lift_snd_assoc, ← F.map_comp]
  have he : F.map (biprod.map a b) = (F.mapBiprod K L).hom ≫
      biprod.map (F.map a) (F.map b) ≫ (F.mapBiprod K' L').inv := by
    apply (cancel_mono (F.mapBiprod K' L').hom).1
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact hn
  have : IsIso (biprod.map (F.map a) (F.map b)) := by
    change IsIso (biprod.mapIso (asIso (F.map a)) (asIso (F.map b))).hom
    infer_instance
  rw [he]
  infer_instance

end SerrePositivity.KST.LocalizingInvariants

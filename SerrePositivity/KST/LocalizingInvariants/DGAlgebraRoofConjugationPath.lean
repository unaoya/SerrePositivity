module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofConjugation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofCellRefinement

/-!
概要：元の実 roof の右三角形を、準同型正方形の右比較の先で実乗法的経路に移す。
方針：左比較の MappingPath 経路と元の右経路を合成し、一回の cell 細分を明示する。
規約：局所化後の等式から経路を選ばない。使われ方：右比較に沿う実経路の反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RoofConjugation
variable (R : Type u) [CommRing R] {A B A' B' E E' : Mon (Complex R)}
  (r : SurjectiveRoof R B' A') (b : B ⟶ B') (a : A ⟶ A') (ha : QuasiIso a.hom)
  (f : A ⟶ E) (g : A' ⟶ E') (c : E ⟶ E') (d : B ⟶ E) (e : B' ⟶ E')
  (hs : f ≫ c = a ≫ g) (hn : b ≫ e = d ≫ c)
  (w : Path.Witness R (r.numerator ≫ g) (r.denominator ≫ e))

def rightPathAfterComparison : Path.Witness R
    (((roof R r b a ha).cellRefinement R 1).numerator ≫ f ≫ c)
    (((roof R r b a ha).cellRefinement R 1).denominator ≫ d ≫ c) := by
  let s := source R r b a ha
  let l := leftPath R r b a ha
  let v := ((MappingPath.pathWitness R a).precomp l).postcomp g
  let z := w.precomp s
  have he : (l ≫ MappingPath.target R a) ≫ g = s ≫ (r.numerator ≫ g) := by
    rw [← source_numerator R r b a ha, Category.assoc]
  let z' : Path.Witness R ((l ≫ MappingPath.target R a) ≫ g)
      (s ≫ (r.denominator ≫ e)) :=
    { hom := z.hom, source_eq := z.source_eq.trans he.symm, target_eq := z.target_eq }
  let vz := v.cellComp R z'
  exact { hom := vz.hom
          source_eq := by
            simpa only [SurjectiveRoof.cellRefinement, iteratedCellAugmentation,
              iteratedCellResolution,
              numerator_eq, l, Category.assoc, hs, Category.comp_id]
              using vz.source_eq
          target_eq := by
            have ht : s ≫ (r.denominator ≫ e) = (roof R r b a ha).denominator ≫ d ≫ c := by
              rw [← Category.assoc, source_denominator, Category.assoc, hn]
            simpa only [SurjectiveRoof.cellRefinement, iteratedCellAugmentation,
              iteratedCellResolution,
              Category.assoc, ht, Category.comp_id] using vz.target_eq }

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RoofConjugation

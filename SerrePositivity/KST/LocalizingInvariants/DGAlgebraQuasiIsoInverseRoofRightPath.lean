module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRoofCellRefinement
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoof

/-!
概要：準同型比較の逆 roof の分子にある cell 経路を、同じ roof の実右三角形へ戻す。
方針：cell 代数の持ち上げと元の MappingPath 経路を合成する。
規約：分母の逆を実代数射とは扱わない。使われ方：二切断の源比較の実反転。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
variable (R : Type u) [CommRing R] {T S A B : Mon (Complex R)} (p : T ⟶ S)
  (hp : QuasiIso p.hom) (a : T ⟶ A) (g : A ⟶ B) (b : S ⟶ B) (n : ℕ)
  (w : Path.Witness R (iteratedCellAugmentation R T n ≫ (a ≫ g))
    (iteratedCellAugmentation R T n ≫ (p ≫ b)))

def inversePostcomposeRightPath : Path.Witness R
    ((((ofQuasiIsoInverse R p hp).postcompose R a).cellRefinement R 2).numerator ≫ g)
    ((((ofQuasiIsoInverse R p hp).postcompose R a).cellRefinement R 2).denominator ≫ b) := by
  let e := iteratedCellAugmentation R T n
  let l := cellResolutionMapLift R (MappingPath.projection R p) e
    (iteratedCellAugmentation_surjective R T n) (iteratedCellAugmentation_quasiIso R T n)
  have hl : l ≫ e = cellAugmentation R (MappingPath.algebra R p) ≫
      MappingPath.projection R p := cellResolutionMapLift_projection R _ _ _ _
  let h := w.precomp l
  let h' : Path.Witness R
      (cellAugmentation R (MappingPath.algebra R p) ≫ ((MappingPath.projection R p ≫ a) ≫ g))
      (cellAugmentation R (MappingPath.algebra R p) ≫ ((MappingPath.projection R p ≫ p) ≫ b)) :=
    { hom := h.hom
      source_eq := h.source_eq.trans (by
        change l ≫ (e ≫ (a ≫ g)) = _
        rw [← Category.assoc, hl]
        simp only [Category.assoc])
      target_eq := h.target_eq.trans (by
        change l ≫ (e ≫ (p ≫ b)) = _
        rw [← Category.assoc, hl]
        simp only [Category.assoc]) }
  let v := ((MappingPath.pathWitness R p).postcomp b).precomp
    (cellAugmentation R (MappingPath.algebra R p))
  let hv := h'.cellComp R v
  exact { hom := hv.hom
          source_eq := by
            simpa only [cellRefinement, postcompose, ofQuasiIsoInverse,
              iteratedCellAugmentation, iteratedCellResolution,
              Category.assoc, Category.comp_id] using hv.source_eq
          target_eq := by
            simpa only [cellRefinement, postcompose, ofQuasiIsoInverse,
              iteratedCellAugmentation, iteratedCellResolution,
              Category.assoc, Category.comp_id] using hv.target_eq }

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof

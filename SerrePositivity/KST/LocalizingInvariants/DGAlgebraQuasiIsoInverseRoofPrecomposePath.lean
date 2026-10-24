module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoofRightPath

/-!
概要：準同型の逆 roof の前合成を、元の roof の実右三角形と両立させる。
方針：合成 roof の実 pullback 射影と MappingPath の元の経路を一回の cell 合成で結ぶ。
規約：元の比較射の逆を実代数射としない。使われ方：二切断の源上段比較を戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof
variable (R : Type u) [CommRing R] {S U A B : Mon (Complex R)}
  (p : S ⟶ U) (hp : QuasiIso p.hom) (r : SurjectiveRoof R S A)
  (g : A ⟶ B) (b : U ⟶ B)
  (w : Path.Witness R (r.numerator ≫ g) (r.denominator ≫ (p ≫ b)))

def inversePrecomposeRightPath : Path.Witness R
    ((((ofQuasiIsoInverse R p hp).comp R r).cellRefinement R 1).numerator ≫ g)
    ((((ofQuasiIsoInverse R p hp).comp R r).cellRefinement R 1).denominator ≫ b) := by
  let l := MonoidPullback.fst (MappingPath.projection R p) r.denominator
  let k := MonoidPullback.snd (MappingPath.projection R p) r.denominator
  have he : l ≫ MappingPath.projection R p = k ≫ r.denominator :=
    MonoidPullback.condition _ _
  let h := w.precomp k
  let h' : Path.Witness R ((k ≫ r.numerator) ≫ g)
      ((l ≫ (MappingPath.projection R p ≫ p)) ≫ b) :=
    { hom := h.hom
      source_eq := h.source_eq.trans (Category.assoc _ _ _).symm
      target_eq := h.target_eq.trans (by
        rw [← Category.assoc k r.denominator, ← he]
        simp only [Category.assoc]) }
  let v := ((MappingPath.pathWitness R p).precomp l).postcomp b
  let hv := h'.cellComp R v
  exact { hom := hv.hom
          source_eq := by
            simpa only [cellRefinement, comp, ofQuasiIsoInverse,
              iteratedCellAugmentation, iteratedCellResolution,
              Category.assoc, Category.comp_id] using hv.source_eq
          target_eq := by
            simpa only [cellRefinement, comp, ofQuasiIsoInverse,
              iteratedCellAugmentation, iteratedCellResolution,
              Category.assoc, Category.comp_id] using hv.target_eq }

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.SurjectiveRoof

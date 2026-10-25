module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.PointHomLiftCoordinates
/-!
概要：既存の標準 Hom の切断から得る native 余錐族の始端と終端を同定する。
方針：InitialTotal の実単体表示と、回収 Hom の固定終点版との比較を使う。
規約：標準の選択済み切断そのものを使用する。普遍性は仮定しない。
使われ方：標準族の右 Hom 比較と左右 Hom 同型を結ぶ高次補正。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)
  (y : (dgNerve R (RightModule R D)) _⦋0⦌)

def dgCoherentBarNativePointHomLiftSimplex {n : ℕ}
    (s : (pinchedHomLeft (dgCoherentBarNormalizedNativeCocone R D F hMC).vertex y) _⦋n⦌) :
    (sliceUnder F) _⦋n + 1⦌ :=
  dgCoherentBarPointLiftSimplex (sliceUnderProjection F)
    (dgCoherentBarNormalizedNativeCocone R D F hMC) y
    ((HomotopyLimits.leftFibrationPointHomLift (sliceUnderProjection F)
      (dgCoherentBarNormalizedNativeCocone R D F hMC) y).app (Opposite.op ⦋n⦌) s)

lemma dgCoherentBarNativePointHomLiftSimplex_source {n : ℕ}
    (s : (pinchedHomLeft (dgCoherentBarNormalizedNativeCocone R D F hMC).vertex y) _⦋n⦌) :
    (sliceUnder F).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (dgCoherentBarNativePointHomLiftSimplex R D F hMC y s) =
        dgCoherentBarNormalizedNativeCocone R D F hMC :=
  dgCoherentBarPointLiftSimplex_source _ _ _ _

lemma dgCoherentBarNativePointHomLiftSimplex_tail {n : ℕ}
    (s : (pinchedHomLeft (dgCoherentBarNormalizedNativeCocone R D F hMC).vertex y) _⦋n⦌) :
    (sliceUnder F).δ 0 (dgCoherentBarNativePointHomLiftSimplex R D F hMC y s) =
      ((HomotopyLimits.coconePointHomFamily
        (dgCoherentBarNormalizedNativeCocone R D F hMC) y).app (Opposite.op ⦋n⦌) s).val :=
  dgCoherentBarPointLiftSimplex_tail _ _ _ _

lemma dgCoherentBarNativePointHomLiftSimplex_source_hom {n : ℕ}
    (s : (pinchedHomLeft (dgCoherentBarNormalizedNativeCocone R D F hMC).vertex y) _⦋n⦌) :
    HEq (dgCoherentBarCoconeLiftHom R D F hMC
      ((sliceUnder F).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
        (dgCoherentBarNativePointHomLiftSimplex R D F hMC y s)))
      (unitElement R (dgCoherentBarNormalizedModule R D F hMC)).val := by
  rw [dgCoherentBarNativePointHomLiftSimplex_source]
  exact (dgCoherentBarCoconeLiftHom_fixed R D F hMC
    (dgCoherentBarNativeApex R D F hMC) (dgCoherentBarNativeCoconePoint R D F hMC)).trans
      (dgCoherentBarNativeCoconePoint_hom R D F hMC)

lemma dgCoherentBarNativePointHomLiftSimplex_tail_hom {n : ℕ}
    (s : (pinchedHomLeft (dgCoherentBarNormalizedNativeCocone R D F hMC).vertex y) _⦋n⦌) :
    HEq (dgCoherentBarCoconeLiftHom R D F hMC
      ((sliceUnder F).δ 0 (dgCoherentBarNativePointHomLiftSimplex R D F hMC y s)))
      (dgCoherentBarCoconeFamilyHom R D F hMC y
        ((HomotopyLimits.coconePointHomFamily
          (dgCoherentBarNormalizedNativeCocone R D F hMC) y).app (Opposite.op ⦋n⦌) s)) := by
  rw [dgCoherentBarNativePointHomLiftSimplex_tail]
  exact dgCoherentBarCoconeLiftHom_fixed R D F hMC y _

end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeHomUniversalColumns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeSubsetCoordinates
/-!
概要：任意の native 余錐の係数から、正規化実 bar を始域とする次数零 Hom 候補を回収する。
方針：非退化係数で全 Hom の逆同値を取り、退化消滅で全単体の成分へ拡張する。
規約：候補の閉性を先取りしない。全 HA 方程式を使った閉性は後続で証明する。
使われ方：native Hom 普遍性の逆写像。
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

def dgCoherentBarCoconeNativeCoefficients (c : JoinCocone F) :
    ∀ s : dgCoherentBarNormalizedIndex I,
      (moduleHom R D (dgCoherentBarSource R D F s.val)
        (dgCoherentBarCoconeModule R D F c)).X (0 - (s.val.1 : ℤ)) :=
  fun s => gradedHomTransport (A := R) (D := RightModule R D) rfl rfl
    (zero_sub (s.val.1 : ℤ)).symm (dgCoherentBarCoconeColumn R D F c s.val)

def dgCoherentBarCoconeHomCandidate (c : JoinCocone F) :
    (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC)
      (dgCoherentBarCoconeModule R D F c)).X 0 :=
  (dgCoherentBarNormalizedNativeHomEquiv R D F hMC (dgCoherentBarCoconeModule R D F c) 0).symm
    (dgCoherentBarCoconeNativeCoefficients R D F c)

lemma dgCoherentBarCoconeHomCandidate_nondegenerate (c : JoinCocone F)
    (s : dgCoherentBarNormalizedIndex I) :
    compose R (x := dgCoherentBarSource R D F s.val)
      (y := dgCoherentBarNormalizedModule R D F hMC) (z := dgCoherentBarCoconeModule R D F c)
      (dgCoherentBarCoconeHomCandidate R D F hMC c)
      (dgCoherentBarNativeColumn R D F hMC s.val)
      (show -(s.val.1 : ℤ) + 0 = 0 - (s.val.1 : ℤ) by omega) =
      dgCoherentBarCoconeNativeCoefficients R D F c s := by
  rw [dgCoherentBarNativeColumn_compose_eq_coordinates, dgCoherentBarCoconeHomCandidate,
    LinearEquiv.apply_symm_apply]

lemma dgCoherentBarCoconeHomCandidate_columns (c : JoinCocone F)
    (s : dgCoherentBarIndex I) :
    compose R (x := dgCoherentBarSource R D F s)
      (y := dgCoherentBarNormalizedModule R D F hMC) (z := dgCoherentBarCoconeModule R D F c)
      (dgCoherentBarCoconeHomCandidate R D F hMC c) (dgCoherentBarNativeColumn R D F hMC s)
      (add_zero (-(s.1 : ℤ))) = dgCoherentBarCoconeColumn R D F c s := by
  classical
  by_cases hs : s.2 ∈ I.nonDegenerate s.1
  · have h := dgCoherentBarCoconeHomCandidate_nondegenerate R D F hMC c ⟨s, hs⟩
    have ht := gradedHomTransport_heq (A := R) (D := RightModule R D) rfl rfl
      (zero_sub (s.1 : ℤ)).symm (dgCoherentBarCoconeColumn R D F c s)
    have he := gradedHom_compose_heq (A := R) (D := RightModule R D)
      (x := dgCoherentBarSource R D F s) (y := dgCoherentBarNormalizedModule R D F hMC)
      (z := dgCoherentBarCoconeModule R D F c)
      (p := -(s.1 : ℤ)) (q := 0) (k := -(s.1 : ℤ))
      (p' := -(s.1 : ℤ)) (q' := 0) (k' := 0 - (s.1 : ℤ))
      rfl rfl rfl rfl rfl (zero_sub (s.1 : ℤ)).symm
      (dgCoherentBarCoconeHomCandidate R D F hMC c) (dgCoherentBarNativeColumn R D F hMC s)
      (dgCoherentBarCoconeHomCandidate R D F hMC c) (dgCoherentBarNativeColumn R D F hMC s)
      HEq.rfl HEq.rfl (add_zero _) (by omega)
    exact eq_of_heq (he.trans ((heq_of_eq h).trans ht))
  · have hd : s.2 ∈ I.degenerate s.1 := by
      simpa only [SSet.nonDegenerate, Set.mem_compl_iff, not_not] using hs
    rw [dgCoherentBarNativeColumn_degenerate R D F hMC ⟨s, hd⟩, DGNerve.compose_zero,
      dgCoherentBarCoconeColumn_degenerate R D F c ⟨s, hd⟩]

end SerrePositivity.InfinityCategories

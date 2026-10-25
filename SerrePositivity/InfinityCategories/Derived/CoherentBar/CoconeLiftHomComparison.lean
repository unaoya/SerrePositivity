module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeLiftHom
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.NativeCoconeFamily
/-!
概要：持ち上げから回収する斉次 Hom を、終点固定版と厳密に比較する。
方針：native 列の成分同値の単射性を、終域と次数の異種等号へ拡張する。
規約：終点の同定を明示し、切断の選択を仮定しない。
使われ方：標準 Hom の持ち上げの終端を既存の全写像空間同型へ戻す。
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

lemma dgCoherentBarNativeColumn_heq_of_index_eq {s t : dgCoherentBarIndex I} (h : s = t) :
    HEq (dgCoherentBarNativeColumn R D F hMC s) (dgCoherentBarNativeColumn R D F hMC t) := by
  cases h
  rfl

lemma dgCoherentBarNativeHom_heq_of_columns {N N' : RightModule R D} {q q' : ℤ}
    (hN : N = N') (hq : q = q')
    (z : (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N).X q)
    (z' : (moduleHom R D (dgCoherentBarNormalizedModule R D F hMC) N').X q')
    (h : ∀ s : dgCoherentBarNormalizedIndex I,
      HEq (compose R (x := dgCoherentBarSource R D F s.val)
        (y := dgCoherentBarNormalizedModule R D F hMC) (z := N) z
        (dgCoherentBarNativeColumn R D F hMC s.val)
        (show -(s.val.1 : ℤ) + q = q - (s.val.1 : ℤ) by omega))
        (compose R (x := dgCoherentBarSource R D F s.val)
          (y := dgCoherentBarNormalizedModule R D F hMC) (z := N') z'
          (dgCoherentBarNativeColumn R D F hMC s.val)
          (show -(s.val.1 : ℤ) + q' = q' - (s.val.1 : ℤ) by omega))) : HEq z z' := by
  cases hN
  cases hq
  apply heq_of_eq
  apply (dgCoherentBarNormalizedNativeHomEquiv R D F hMC N q).injective
  funext s
  rw [← dgCoherentBarNativeColumn_compose_eq_coordinates,
    ← dgCoherentBarNativeColumn_compose_eq_coordinates]
  exact eq_of_heq (h s)

lemma dgCoherentBarCoconeLiftTarget_fixed {m : ℕ}
    (y : (dgNerve R (RightModule R D)) _⦋0⦌)
    (c : (coconeMappingSpace F y) _⦋m⦌) :
    dgCoherentBarCoconeLiftTarget R D F c.val = dgNerve.vertexEquiv R (RightModule R D) y := by
  unfold dgCoherentBarCoconeLiftTarget
  rw [c.property]
  rfl

lemma dgCoherentBarCoconeLiftColumn_fixed {m : ℕ}
    (y : (dgNerve R (RightModule R D)) _⦋0⦌)
    (c : (coconeMappingSpace F y) _⦋m⦌) (s : dgCoherentBarIndex I) :
    HEq (dgCoherentBarCoconeLiftColumn R D F c.val s)
      (dgCoherentBarCoconeFamilyColumn R D F y c s) := by
  unfold dgCoherentBarCoconeLiftColumn dgCoherentBarCoconeFamilyColumn
  exact (gradedHomTransport_heq _ _ _ _).trans (gradedHomTransport_heq _ _ _ _).symm

lemma dgCoherentBarCoconeLiftHom_fixed {m : ℕ}
    (y : (dgNerve R (RightModule R D)) _⦋0⦌)
    (c : (coconeMappingSpace F y) _⦋m⦌) :
    HEq (dgCoherentBarCoconeLiftHom R D F hMC c.val)
      (dgCoherentBarCoconeFamilyHom R D F hMC y c) := by
  apply dgCoherentBarNativeHom_heq_of_columns R D F hMC
    (dgCoherentBarCoconeLiftTarget_fixed R D F y c) rfl
  intro s
  have hL := dgCoherentBarCoconeLiftHom_nondegenerate R D F hMC c.val s
  have hR := dgCoherentBarCoconeFamilyHom_nondegenerate R D F hMC y c s
  exact (heq_of_eq hL).trans
    ((dgCoherentBarCoconeLiftColumn_fixed R D F y c s.val).trans
      (heq_of_eq hR).symm)

end SerrePositivity.InfinityCategories

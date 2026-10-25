module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseMixedNaturality
/-!
概要：逆データの二変数添字変更を、純粋な左右の面で比較する。
方針：join の包含と添字変更の可換性を、引き戻しの合成則へ代入する。
規約：ここでは単射性を仮定しない。
使われ方：逆データ全体の二変数自然性の純粋な面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial

lemma dgCoherentBarJoin_pullback_left {R : Type u} [CommRing R]
    {C : Type v} [DGCategory R C] {a b n m : ℕ} (s : SimplexData R C (n + m + 1))
    (α : Fin (a + 1) →o Fin (n + 1)) (β : Fin (b + 1) →o Fin (m + 1)) :
    (s.pullback (dgCoherentBarJoinOrderMap α β)).pullback (dgCoherentBarJoinLeft a b) =
      (s.pullback (dgCoherentBarJoinLeft n m)).pullback α := by
  rw [SimplexData.pullback_comp, SimplexData.pullback_comp]
  congr 1
  apply DFunLike.ext
  intro i
  exact dgCoherentBarJoinOrderMap_left α β i

lemma dgCoherentBarJoin_pullback_right {R : Type u} [CommRing R]
    {C : Type v} [DGCategory R C] {a b n m : ℕ} (s : SimplexData R C (n + m + 1))
    (α : Fin (a + 1) →o Fin (n + 1)) (β : Fin (b + 1) →o Fin (m + 1)) :
    (s.pullback (dgCoherentBarJoinOrderMap α β)).pullback (dgCoherentBarJoinRight a b) =
      (s.pullback (dgCoherentBarJoinRight n m)).pullback β := by
  rw [SimplexData.pullback_comp, SimplexData.pullback_comp]
  congr 1
  apply DFunLike.ext
  intro i
  exact dgCoherentBarJoinOrderMap_right α β i

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

lemma dgCoherentBarInverseRawData_map_left {a b n m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1)) :
    (dgCoherentBarInverseRawData R D F hMC N (DGNerve.PinchedHom.LinearData.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s)).pullback (dgCoherentBarJoinLeft a b) =
    ((dgCoherentBarInverseRawData R D F hMC N f s).pullback
      (dgCoherentBarJoinOrderMap α β)).pullback (dgCoherentBarJoinLeft a b) := by
  rw [dgCoherentBarJoin_pullback_left, dgCoherentBarInverseRawData_left,
    dgCoherentBarInverseRawData_left]
  exact congrArg DGNerve.Simplex.toSimplexData (coherentDiagramSimplex_map F α s)

lemma dgCoherentBarInverseRawData_map_right {a b n m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) (α : Fin (a + 1) →o Fin (n + 1))
    (β : Fin (b + 1) →o Fin (m + 1)) :
    (dgCoherentBarInverseRawData R D F hMC N (DGNerve.PinchedHom.LinearData.pullback β f)
      (I.map (SimplexCategory.mkHom α).op s)).pullback (dgCoherentBarJoinRight a b) =
    ((dgCoherentBarInverseRawData R D F hMC N f s).pullback
      (dgCoherentBarJoinOrderMap α β)).pullback (dgCoherentBarJoinRight a b) := by
  rw [dgCoherentBarJoin_pullback_right, dgCoherentBarInverseRawData_right,
    dgCoherentBarInverseRawData_right]
  have h := InfinityCategories.PinchedHom.constant_pullback
    (X := dgNerve R (RightModule R D)) (x := Simplex.vertex (A := R) N)
    (SimplexCategory.mkHom β)
  exact (congrArg DGNerve.Simplex.toSimplexData h).symm

end SerrePositivity.InfinityCategories

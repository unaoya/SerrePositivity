module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseParameterTerm
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.ParameterBoundarySum
/-!
概要：逆構成の混合 HA 右辺のパラメーター側の和を、全標準面の高次 Hom の符号付き和へ同定する。
方針：全内部頂点の比較を有限和へ束ね、最後の切断補正を最終面へ移す。
規約：正次数の任意の線形成分族を扱う。
使われ方：高次 Hom の微分が全標準面の境界に一致することの証明。
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
  (N : RightModule R D)

lemma dgCoherentBarInverse_parameter_sum {m n : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N (m + 1))
    (s : I _⦋n⦌) :
    HEq (∑ j : Fin (m + 1), dgCoherentBarFullTerm
      (dgCoherentBarInverseRawData R D F hMC N f s) (j.natAdd n))
      (∑ a : Fin (m + 2), (((m + 1 : ℕ) : ℤ) - (a.val : ℤ)).negOnePow •
        dgCoherentBarInverseFaceColumn R D F hMC N f s a) := by
  have h := sum_heq_of_obj_eq
    (dgCoherentBarInverseRawData_source R D F hMC N f s)
    (dgCoherentBarInverseRawData_target R D F hMC N f s)
    (fun j : Fin (m + 1) => dgCoherentBarFullTerm
      (dgCoherentBarInverseRawData R D F hMC N f s) (j.natAdd n))
    (fun j : Fin (m + 1) => (((m + 1 : ℕ) : ℤ) - (j.val : ℤ)).negOnePow •
      (dgCoherentBarInverseFaceColumn R D F hMC N f s j.castSucc -
        if j = Fin.last m then dgCoherentBarInverseFaceColumn R D F hMC N f s
          (Fin.last (m + 1)) else 0))
    (fun j => dgCoherentBarInverseFullTerm_parameter R D F hMC N f s j)
  rw [dgCoherentBarParameter_boundary_sum] at h
  exact h

end SerrePositivity.InfinityCategories

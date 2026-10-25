module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.InverseMixedColumns
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.JoinRawCoordinates
/-!
概要：任意の pinched 線形単体から、逆比較の全 join 単体データを構成する。
方針：元の図式の純粋な面・定値終点の面・native 列との混合合成を貼り合わせる。
規約：正規化加群の公開型を維持し、HA 方程式は後続で証明する。
使われ方：工程Bの高次逆射の候補。
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
  (hMC : dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

def dgCoherentBarInverseMixedData {n m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    DGCoherentBarJoinMixedData (coherentDiagramSimplex F s).toSimplexData
      (InfinityCategories.PinchedHom.constant
        (X := dgNerve R (RightModule R D)) (Simplex.vertex (A := R) N) m).toSimplexData := by
  intro K L hK hL k hk
  let r := K.card - 1
  have hc : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  exact gradedHomTransport (dgCoherentBarSubsetLabel_source R D F s K r hc hK)
    rfl (show 1 - (L.card : ℤ) - (r : ℤ) = k by
      rw [hc] at hk; push_cast at hk; omega)
    (dgCoherentBarInverseMixedColumn R D F hMC N f L (1 - (L.card : ℤ)) hL rfl
      (dgCoherentBarSubsetLabel s K r hc))

def dgCoherentBarInverseRawData {n m : ℕ}
    (f : DGNerve.PinchedHom.LinearData R (dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) : SimplexData R (RightModule R D) (n + m + 1) :=
  dgCoherentBarJoinRawData (coherentDiagramSimplex F s).toSimplexData
    (InfinityCategories.PinchedHom.constant
        (X := dgNerve R (RightModule R D)) (Simplex.vertex (A := R) N) m).toSimplexData
    (dgCoherentBarInverseMixedData R D F hMC N f s)

end SerrePositivity.InfinityCategories

module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseMixedColumns
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinRawCoordinates
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory Limits DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F) (N : RightModule R D)

def dgCoherentBarInverseMixedData {n m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.DGCoherentBarJoinMixedData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s).toSimplexData
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) N) m).toSimplexData := by
  intro K L hK hL k hk
  let r := K.card - 1
  have hc : K.card = r + 1 := by have := Finset.card_pos.mpr hK; dsimp [r]; omega
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel_source R D F s K r hc hK)
    rfl (show 1 - (L.card : ℤ) - (r : ℤ) = k by
      rw [hc] at hk; push_cast at hk; omega)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseMixedColumn R D F hMC N f L (1 - (L.card : ℤ)) hL rfl
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel s K r hc))

def dgCoherentBarInverseRawData {n m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) (n + m + 1) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRawData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s).toSimplexData
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant
        (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) N) m).toSimplexData
    (dgCoherentBarInverseMixedData R D F hMC N f s)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

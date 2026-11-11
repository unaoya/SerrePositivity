module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.InverseNativeFactorization
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.JoinRawRestrictions
/-!
概要：逆構成した単体データの左右の面と実端点、全パラメーター係数を固定する。
方針：join 貼り合わせの制限と、左右の包含の頂点公式を使う。
規約：任意の線形成分族に適用する。
使われ方：逆構成の HA 各項の比較。
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

lemma dgCoherentBarInverseRawData_left {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s).pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinLeft n m) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex F s).toSimplexData := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRawData_left _ _ _

lemma dgCoherentBarInverseRawData_right {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s).pullback (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) N) m).toSimplexData := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRawData_right _ _ _

lemma dgCoherentBarInverseRawData_source {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s).obj 0 =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F ⟨n, s⟩ := by
  have h := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) n => t.obj 0)
    (dgCoherentBarInverseRawData_left R D F hMC N f s)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramSimplex_obj F s 0)

lemma dgCoherentBarInverseRawData_target {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s).obj (Fin.last (n + m + 1)) = N := by
  have h := congrArg (fun t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) m => t.obj (Fin.last m))
    (dgCoherentBarInverseRawData_right R D F hMC N f s)
  have he : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m (Fin.last m) = Fin.last (n + m + 1) :=
    Fin.ext (by dsimp [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinRightOrderHom]; omega)
  change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseRawData R D F hMC N f s).obj
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinRight n m (Fin.last m)) = N at h
  rwa [he] at h

abbrev dgCoherentBarInverseFullHom {m : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseParameterCoefficient f Finset.univ (-(m : ℤ))
    Finset.univ_nonempty (by simp)

abbrev dgCoherentBarInverseFullHomAt {m n : ℕ}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) N m)
    (s : I _⦋n⦌) := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarInverseParameterHomAt R D F hMC N f Finset.univ
      (-(m : ℤ)) Finset.univ_nonempty (by simp) s

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

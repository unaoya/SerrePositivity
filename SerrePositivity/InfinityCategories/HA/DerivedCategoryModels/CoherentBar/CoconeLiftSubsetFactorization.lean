module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeRecoveredCoordinates
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeLiftFactorization
/-!
概要：持ち上げ余錐の全混合成分を、回収した右部分集合の Hom と native 列に分解する。
方針：混合部分単体の成分回収と native Hom の一意性を合成する。
規約：動く終域の輸送を明示し、全非空部分集合を扱う。
使われ方：パラメーター削除項と切断項を一点下の回収データへ移す。
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
  (hMC : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarMaurerCartan R D F)

lemma dgCoherentBarCoconeLiftSimplex_subset_factorization {m n r l : ℕ}
    (c : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F) _⦋m⦌) (s : I _⦋n⦌)
    (K : Finset (Fin (n + 1))) (L : Finset (Fin (m + 1)))
    (hcK : K.card = r + 1) (hcL : L.card = l + 1) (hL : L.Nonempty)
    (a b : Fin (n + m + 1 + 1)) (k : ℤ)
    (hJ : 2 ≤ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card)
    (ha : a = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hb : b = (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L).card : ℤ)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex R D F c s).hom
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarJoinSubset K L) a b k hJ ha hb hk)
      (_root_.SerrePositivity.DifferentialGraded.compose R
        (x := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D F (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel s K r hcK))
        (y := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC)
        (z := ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F).app (Opposite.op ⦋m⦌) c).obj (L.max' hL))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(l : ℤ)) hL
          (by rw [hcL]; push_cast; omega))
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel s K r hcK))
        (show -(r : ℤ) + -(l : ℤ) = -(l : ℤ) - (r : ℤ) by omega)) := by
  let c' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder F).map (SimplexCategory.mkHom
    (L.orderEmbOfFin hcL).toOrderHom).op c
  let τ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSubsetLabel s K r hcK
  have hColumns := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom_columns R D F hMC c' τ
  have hPhi := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom_heq R D F hMC c L (-(l : ℤ)) hL
    (by rw [hcL]; push_cast; omega) hcL
  have hTarget := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftTarget_subset R D F c L hcL hL
  have hCompose := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
    rfl rfl hTarget.symm rfl rfl rfl
    (p := -(r : ℤ)) (q := -(l : ℤ)) (k := -(l : ℤ) - (r : ℤ))
    (p' := -(r : ℤ)) (q' := -(l : ℤ)) (k' := -(l : ℤ) - (r : ℤ))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSubsetHom R D F hMC c L (-(l : ℤ)) hL
      (by rw [hcL]; push_cast; omega))
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC τ)
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftHom R D F hMC c')
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeColumn R D F hMC τ) hPhi HEq.rfl (by omega) (by omega)
  exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeLiftSimplex_mixed_hom_heq R D F c s K L hcK hcL
    a b k hJ ha hb hk).trans ((heq_of_eq hColumns).symm.trans hCompose.symm)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

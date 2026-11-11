module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.CoconeHomCandidate
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.LastPostcompositionResidual
/-!
概要：回収した Hom 候補で正規化 native 単体を後合成すると、元の任意余錐の全単体を回収する。
方針：先頭面と末端対象を固定し、全末端部分集合で同じ係数になることを使う。
規約：候補の閉性をこの段階で仮定しない。
使われ方：元の HA 方程式から候補の微分が全 native 列を消すことを導く。
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

def dgCoherentBarCoconeCandidateAt (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {n : ℕ} (s : I _⦋n⦌) :
    GradedHom R ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).obj (Fin.last (n + 1)))
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeModule R D F c) 0 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_last R D F hMC s).symm rfl rfl
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeHomCandidate R D F hMC c)

lemma dgCoherentBarCoconeCandidateAt_heq (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {n : ℕ} (s : I _⦋n⦌) :
    HEq (dgCoherentBarCoconeCandidateAt R D F hMC c s)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeHomCandidate R D F hMC c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHomTransport_heq _ _ _ _

def dgCoherentBarCoconeRestoredData (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {n : ℕ} (s : I _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) (n + 1) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPostLastData (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeModule R D F c) (dgCoherentBarCoconeCandidateAt R D F hMC c s)

lemma dgCoherentBarCoconeRestoredData_eq (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) {n : ℕ} (σ : I _⦋n⦌) :
    dgCoherentBarCoconeRestoredData R D F hMC c σ =
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c σ).toSimplexData := by
  let s := dgCoherentBarCoconeRestoredData R D F hMC c σ
  let t := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex R D F c σ).toSimplexData
  have hfront : s.pullback Fin.castSuccOrderEmb.toOrderHom =
      t.pullback Fin.castSuccOrderEmb.toOrderHom := by
    change (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPostLastData _ _ _).pullback _ = _
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPostLastData_front]
    exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData_front R D F hMC σ).trans
      (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex_front R D F c σ)).symm
  have hobj : s.obj = t.obj := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_last
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC σ).toSimplexData
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeModule R D F c)).trans
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex_last R D F c σ).symm
    | cast i =>
      exact congrArg (fun u : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R (RightModule R D) n => u.obj i) hfront
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomFamily.heq_of_pointwise hobj
  intro J a b k hJ ha hb hk
  by_cases hbl : b = Fin.last (n + 1)
  · cases hbl
    have hx := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.lastReplacementObj_of_ne (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarBianchiData R D F σ)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNormalizedModule R D F hMC) a (ha ▸ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.min_ne_last J hJ)).trans
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarBianchiLabel_source R D F σ J a hJ ha hb)
    have hy := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex_last R D F hMC σ
    have hd := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarBianchiLabel_degree σ J hJ hb k hk
    have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.gradedHom_compose_heq (A := R) (D := RightModule R D)
      hx hy rfl hd rfl hd _ _ _ _ (dgCoherentBarCoconeCandidateAt_heq R D F hMC c σ)
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplexData_last_hom_heq R D F hMC σ J a k hJ ha hb hk)
      (add_zero k) (add_zero _)
    refine (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarPostLastData_hom_last
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarNativeSimplex R D F hMC σ).toSimplexData
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeModule R D F c) (dgCoherentBarCoconeCandidateAt R D F hMC c σ)
      J a k hJ ha hb hk).trans (hc.trans ?_)
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeHomCandidate_columns]
    exact (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarCoconeSimplex_last_hom_heq R D F c σ J a k hJ ha hb hk).symm
  · have hnot : Fin.last (n + 1) ∉ J := by
      intro hl
      have hle : Fin.last (n + 1) ≤ b := by rw [hb]; exact Finset.le_max' J _ hl
      exact hbl (le_antisymm (Fin.le_last _) hle)
    have hc : (Fin.last (n + 1)).succAboveOrderEmb.toOrderHom =
        Fin.castSuccOrderEmb.toOrderHom := by
      apply DFunLike.ext
      intro i
      exact congrFun Fin.succAbove_last i
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.hom_heq_of_face_pullback_eq s t (Fin.last (n + 1))
      (by simpa only [hc] using hfront) J hnot a b k hJ ha hb hk

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar

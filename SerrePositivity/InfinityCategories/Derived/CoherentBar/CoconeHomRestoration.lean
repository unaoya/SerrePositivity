module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.CoconeHomCandidate
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.LastPostcompositionResidual
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))
  (hMC : dgCoherentBarMaurerCartan R D F)

def dgCoherentBarCoconeCandidateAt (c : JoinCocone F) {n : ℕ} (s : I _⦋n⦌) :
    GradedHom R ((dgCoherentBarNativeSimplex R D F hMC s).obj (Fin.last (n + 1)))
      (dgCoherentBarCoconeModule R D F c) 0 :=
  gradedHomTransport (dgCoherentBarNativeSimplex_last R D F hMC s).symm rfl rfl
    (dgCoherentBarCoconeHomCandidate R D F hMC c)

lemma dgCoherentBarCoconeCandidateAt_heq (c : JoinCocone F) {n : ℕ} (s : I _⦋n⦌) :
    HEq (dgCoherentBarCoconeCandidateAt R D F hMC c s)
      (dgCoherentBarCoconeHomCandidate R D F hMC c) :=
  gradedHomTransport_heq _ _ _ _

def dgCoherentBarCoconeRestoredData (c : JoinCocone F) {n : ℕ} (s : I _⦋n⦌) :
    SimplexData R (RightModule R D) (n + 1) :=
  dgCoherentBarPostLastData (dgCoherentBarNativeSimplex R D F hMC s).toSimplexData
    (dgCoherentBarCoconeModule R D F c) (dgCoherentBarCoconeCandidateAt R D F hMC c s)

lemma dgCoherentBarCoconeRestoredData_eq (c : JoinCocone F) {n : ℕ} (σ : I _⦋n⦌) :
    dgCoherentBarCoconeRestoredData R D F hMC c σ =
      (dgCoherentBarCoconeSimplex R D F c σ).toSimplexData := by
  let s := dgCoherentBarCoconeRestoredData R D F hMC c σ
  let t := (dgCoherentBarCoconeSimplex R D F c σ).toSimplexData
  have hfront : s.pullback Fin.castSuccOrderEmb.toOrderHom =
      t.pullback Fin.castSuccOrderEmb.toOrderHom := by
    change (dgCoherentBarPostLastData _ _ _).pullback _ = _
    rw [dgCoherentBarPostLastData_front]
    exact (dgCoherentBarNativeSimplexData_front R D F hMC σ).trans
      (congrArg DGNerve.Simplex.toSimplexData
        (dgCoherentBarCoconeSimplex_front R D F c σ)).symm
  have hobj : s.obj = t.obj := by
    funext i
    induction i using Fin.lastCases with
    | last =>
      exact (SimplexData.lastReplacementObj_last
        (dgCoherentBarNativeSimplex R D F hMC σ).toSimplexData
        (dgCoherentBarCoconeModule R D F c)).trans
        (dgCoherentBarCoconeSimplex_last R D F c σ).symm
    | cast i =>
      exact congrArg (fun u : SimplexData R (RightModule R D) n => u.obj i) hfront
  apply SimplexData.ext hobj
  apply HomFamily.heq_of_pointwise hobj
  intro J a b k hJ ha hb hk
  by_cases hbl : b = Fin.last (n + 1)
  · cases hbl
    have hx := (SimplexData.lastReplacementObj_of_ne (dgCoherentBarBianchiData R D F σ)
      (dgCoherentBarNormalizedModule R D F hMC) a (ha ▸ PinchedHom.min_ne_last J hJ)).trans
      (dgCoherentBarBianchiLabel_source R D F σ J a hJ ha hb)
    have hy := dgCoherentBarNativeSimplex_last R D F hMC σ
    have hd := dgCoherentBarBianchiLabel_degree σ J hJ hb k hk
    have hc := gradedHom_compose_heq (A := R) (D := RightModule R D)
      hx hy rfl hd rfl hd _ _ _ _ (dgCoherentBarCoconeCandidateAt_heq R D F hMC c σ)
      (dgCoherentBarNativeSimplexData_last_hom_heq R D F hMC σ J a k hJ ha hb hk)
      (add_zero k) (add_zero _)
    refine (dgCoherentBarPostLastData_hom_last
      (dgCoherentBarNativeSimplex R D F hMC σ).toSimplexData
      (dgCoherentBarCoconeModule R D F c) (dgCoherentBarCoconeCandidateAt R D F hMC c σ)
      J a k hJ ha hb hk).trans (hc.trans ?_)
    rw [dgCoherentBarCoconeHomCandidate_columns]
    exact (dgCoherentBarCoconeSimplex_last_hom_heq R D F c σ J a k hJ ha hb hk).symm
  · have hnot : Fin.last (n + 1) ∉ J := by
      intro hl
      have hle : Fin.last (n + 1) ≤ b := by rw [hb]; exact Finset.le_max' J _ hl
      exact hbl (le_antisymm (Fin.le_last _) hle)
    have hc : (Fin.last (n + 1)).succAboveOrderEmb.toOrderHom =
        Fin.castSuccOrderEmb.toOrderHom := by
      apply DFunLike.ext
      intro i
      exact congrFun Fin.succAbove_last i
    exact SimplexData.hom_heq_of_face_pullback_eq s t (Fin.last (n + 1))
      (by simpa only [hc] using hfront) J hnot a b k hJ ha hb hk

end SerrePositivity.InfinityCategories

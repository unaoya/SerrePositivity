module
public import SerrePositivity.KST.SConstruction.PathFirstFaceHomotopyPullback
public import SerrePositivity.KST.SConstruction.SimplicialCartesianNaturality

/-! # 元の経路境界の全単体作用素の面条件
概要：正の反復実現後の元の経路境界は全ての単体作用素で homotopy-cartesian。
方針：δ₀ は連結基底での退縮検出、残る面と退化は先頭を保つ Segal 積座標で証明し合成する。
規約：追加の面条件を仮定しない。使われ方：既存の Segal 実現定理と homotopy fiber の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.KST.Comparison
open scoped Simplicial

/-- 元の経路境界の全ての面の四角形は正の反復実現後に homotopy pullback。 -/
lemma iteratedPathBoundary_face_homotopyPullback (r n : ℕ) (i : Fin (n + 2))
    (X : StableModel.{u}) : IsHomotopyPullback
      (CommSq.mk ((iteratedPathBoundary (r + 1) X).naturality (SimplexCategory.δ i).op)) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact iteratedPathBoundary_firstFace_homotopyPullback r n X
  · apply iteratedPathBoundary_headPreserving_homotopyPullback r (SimplexCategory.δ j.succ) ?_ X
    exact Fin.succ_succAbove_zero j

/-- 元の経路境界の全ての退化の四角形は正の反復実現後に homotopy pullback。 -/
lemma iteratedPathBoundary_degeneracy_homotopyPullback (r n : ℕ) (i : Fin (n + 1))
    (X : StableModel.{u}) : IsHomotopyPullback
      (CommSq.mk ((iteratedPathBoundary (r + 1) X).naturality (SimplexCategory.σ i).op)) := by
  apply iteratedPathBoundary_headPreserving_homotopyPullback r (SimplexCategory.σ i) ?_ X
  simp [SimplexCategory.σ]

/-- 元の経路境界は正の全有限反復実現後に全ての単体作用素で homotopy-cartesian。 -/
lemma iteratedPathBoundary_homotopyPullback (r : ℕ) (X : StableModel.{u})
    {d e : SimplexCategory} (θ : d ⟶ e) :
    IsHomotopyPullback (CommSq.mk ((iteratedPathBoundary (r + 1) X).naturality θ.op)) :=
  simplicial_naturality_homotopyPullback_of_generators (iteratedPathBoundary (r + 1) X)
    (fun n i => iteratedPathBoundary_face_homotopyPullback r n i X)
    (fun n i => iteratedPathBoundary_degeneracy_homotopyPullback r n i X) θ

end SerrePositivity.KST.SConstruction

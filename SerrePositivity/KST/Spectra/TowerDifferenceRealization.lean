module

public import SerrePositivity.KST.Spectra.TowerDifferenceRealizationStep

/-!
概要：任意の高次ホモトピー群の族を、厳密に整合する球面の零ホモトピーの差で実現する。
方針：初段を定数球面とし、指定した差を持つ次段の構成を自然数で反復する。
規約：球面は厳密に射影されるが、零ホモトピーの隣接差は指定した任意の族となる。
使われ方：Goerss–Jardine VIII §1。塔の核から lim¹ への障害の全射性の入力。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedFibrationTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ)
  (a : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)

/-- 指定した隣接差を実現する球面と零ホモトピーを逐次選ぶ。 -/
def differenceRealizationStage : ∀ n, NullSphereStage (X n) r
  | 0 => ⟨.const, PtSimplex.RelStruct.refl .const (Fin.last (r + 1))⟩
  | n + 1 => Classical.choose
      (exists_difference_step (p n) (differenceRealizationStage n) (a n))

/-- 選んだ球面は、ホモトピー類だけでなく単体として厳密に整合する。 -/
lemma differenceRealizationStage_comp (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
      (differenceRealizationStage X p r a (n + 1)).1 =
    (differenceRealizationStage X p r a n).1 :=
  Classical.choose (Classical.choose_spec
    (exists_difference_step (p n) (differenceRealizationStage X p r a n) (a n)))

/-- 選んだ零ホモトピーの差は指定した族そのもの。 -/
lemma differenceRealizationStage_difference (n : ℕ) :
    NullHomotopyDifference.difference (differenceRealizationStage X p r a n).2
      (NullHomotopyDifference.mapNullTo (p n).right
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n)) (differenceRealizationStage_comp X p r a n)
        (differenceRealizationStage X p r a (n + 1)).2) = a n :=
  Classical.choose_spec (Classical.choose_spec
    (exists_difference_step (p n) (differenceRealizationStage X p r a n) (a n)))

/-- 任意の族は、厳密に整合する球面の零ホモトピーの隣接差の族として実現できる。 -/
theorem exists_nullHomotopyDifferenceFamily :
    ∃ s : ∀ n, (X n).right.PtSimplex (r + 1) (X n).basepoint,
      ∃ hs : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
        (s (n + 1)) = s n,
      ∃ R : ∀ n, PtSimplex.RelStruct .const (s n) (Fin.last (r + 1)),
        nullHomotopyDifferenceFamily X p r s hs R = a := by
  refine ⟨fun n ↦ (differenceRealizationStage X p r a n).1,
    differenceRealizationStage_comp X p r a,
    fun n ↦ (differenceRealizationStage X p r a n).2, ?_⟩
  funext n
  exact differenceRealizationStage_difference X p r a n

end
end SerrePositivity.KST.Spectra.PointedFibrationTower

module

public import SerrePositivity.KST.Spectra.TowerKernelObstruction
public import SerrePositivity.KST.Spectra.TowerStrictNullHomotopies
public import SerrePositivity.KST.Spectra.TowerRelativeHomotopyLimit

/-!
概要：比較の核の lim¹ 障害が零であることと、極限の類の零性の同値。
方針：零障害から整合する零ホモトピーを構成し、実際の極限の RelStruct へ組み立てる。
規約：lim¹ との全単射は含めない。零障害を検出する方向を両向きに証明する。
使われ方：Goerss–Jardine VIII §1。Milnor 比較の単射性と収束判定。
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

/-- 核の球面代表の障害が零なら、極限で実際に零ホモトピック。 -/
theorem exists_limit_nullHomotopy_of_obstruction_eq_point
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)).PtSimplex
      (r + 1) (limitBasepoint X p))
    (hs : limitGroupComparison X p r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = 1)
    (hz : kernelRepresentativeObstruction X p r s hs = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _) :
    Nonempty (PtSimplex.RelStruct .const s (Fin.last (r + 1))) := by
  obtain ⟨U, hU⟩ := exists_compatible_nullHomotopies X p r (projectedSimplex X p r s)
    (projectedSimplex_comp X p r s) (projectedNullHomotopy X p r s hs) hz
  let U' n : PtSimplex.RelStruct
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n)
        rfl (.const : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right)
          (fun n ↦ (p n).right)).PtSimplex (r + 1) (limitBasepoint X p)))
      (projectedSimplex X p r s n) (Fin.last (r + 1)) := {
    map := (U n).map
    δ_castSucc_map := by rw [(U n).δ_castSucc_map]; rfl
    δ_succ_map := (U n).δ_succ_map
    δ_map_of_lt := (U n).δ_map_of_lt
    δ_map_of_gt := (U n).δ_map_of_gt }
  exact ⟨limitRelStruct X p r .const s U' hU⟩

/-- 核の球面代表の零障害判定。 -/
theorem kernelRepresentativeObstruction_eq_point_iff
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)).PtSimplex
      (r + 1) (limitBasepoint X p))
    (hs : limitGroupComparison X p r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = 1) :
    kernelRepresentativeObstruction X p r s hs = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = 1 := by
  constructor
  · intro hz
    obtain ⟨R⟩ := exists_limit_nullHomotopy_of_obstruction_eq_point X p r s hs hz
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound R).symm
  · exact kernelRepresentativeObstruction_eq_point_of_mk_eq_one X p r s hs

/-- 核上の障害写像は、基点の逆像が単位元だけである。 -/
theorem kernelObstruction_eq_point_iff (b : (limitGroupComparison X p r).ker) :
    kernelObstruction X p r b = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ ↔ b = 1 := by
  constructor
  · intro hz
    apply Subtype.ext
    exact (kernelSphereRepresentative_mk X p r b).symm.trans
      ((kernelRepresentativeObstruction_eq_point_iff X p r _ _).1 hz)
  · rintro rfl
    exact kernelObstruction_one X p r

/-- lim¹ が消滅する塔では極限のホモトピー群の比較は単射。 -/
theorem limitGroupComparison_injective_of_limOne_subsingleton
    (hlim : Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n)))) :
    Function.Injective (limitGroupComparison X p r) := by
  intro a b hab
  have hc : limitGroupComparison X p r (a * b⁻¹) = 1 := by
    rw [map_mul, map_inv, hab, mul_inv_cancel]
  have hk : (⟨a * b⁻¹, hc⟩ : (limitGroupComparison X p r).ker) = 1 :=
    (kernelObstruction_eq_point_iff X p r _).1 (hlim.elim _ _)
  exact mul_inv_eq_one.mp (congrArg Subtype.val hk)

/-- 次のホモトピー次数の遷移が全射なら、極限との比較は全単射。 -/
theorem limitGroupComparison_bijective_of_surjective
    (hq : ∀ n, Function.Surjective (pointedGroupMap (r + 1) (p n))) :
    Function.Bijective (limitGroupComparison X p r) :=
  ⟨limitGroupComparison_injective_of_limOne_subsingleton X p r
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.subsingleton_of_surjective _ _ hq), limitGroupComparison_surjective X p r⟩

/-- 次の次数で全射な塔に対する、極限のホモトピー群と群の逆極限の同型。 -/
def limitGroupEquivOfSurjective
    (hq : ∀ n, Function.Surjective (pointedGroupMap (r + 1) (p n))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right))
      r (limitBasepoint X p) ≃* compatibleGroup X p r :=
  MulEquiv.ofBijective (limitGroupComparison X p r)
    (limitGroupComparison_bijective_of_surjective X p r hq)

end
end SerrePositivity.KST.Spectra.PointedFibrationTower

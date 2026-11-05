module

public import SerrePositivity.KST.Spectra.TowerNullHomotopyObstruction
public import SerrePositivity.KST.Spectra.TowerGroupLimitComparison

/-!
概要：塔の比較の核の球面代表から lim¹ の障害を構成する。
方針：各射影の零性から零ホモトピーを選び、選択によらない差の軌道へ送る。
規約：球面代表は固定する。代表変更への不変性と核との全単射はまだ含まない。
使われ方：Goerss–Jardine VIII §1。Milnor の比較の核の幾何的な障害。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.PointedFibrationTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n) (r : ℕ)
  (s : (FibrationTower.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)).PtSimplex
    (r + 1) (limitBasepoint X p))

/-- 極限の球面の各段への厳密な射影。 -/
def projectedSimplex (n : ℕ) : (X n).right.PtSimplex (r + 1) (X n).basepoint :=
  mapSimplex (FibrationTower.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n) rfl s

/-- 極限の球面の各射影は、単体として厳密に整合する。 -/
lemma projectedSimplex_comp (n : ℕ) :
    mapSimplex (p n).right (OmegaSpectrum.pointedMap_basepoint (p n))
      (projectedSimplex X p r s (n + 1)) = projectedSimplex X p r s n := by
  apply RelativeMorphism.ext
  change (s.map ≫ FibrationTower.projection _ _ (n + 1)) ≫ (p n).right =
    s.map ≫ FibrationTower.projection _ _ n
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kan.FibrationTower.projection_comp]

variable [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right]
  (hzero : limitGroupComparison X p r (KanHomotopyGroup.mk s) = 1)

include hzero in
/-- 比較の核の代表の各段には、実際の零ホモトピーが存在する。 -/
lemma exists_projected_nullHomotopy (n : ℕ) :
    Nonempty (PtSimplex.RelStruct .const (projectedSimplex X p r s n) (Fin.last (r + 1))) := by
  have he := (limitGroupComparison_eq_one_iff X p r (KanHomotopyGroup.mk s)).1 hzero n
  change KanHomotopyGroup.map _ rfl (KanHomotopyGroup.mk s) = 1 at he
  rw [_root_.SerrePositivity.InfinityCategories.Kan.KanHomotopyGroup.map_mk] at he
  apply (simplexRel_iff_relStruct (Fin.last (r + 1))).1
  apply (KanHomotopyGroup.mk_eq_iff _ _).1
  exact he.symm

/-- 比較の核の代表に対して各段の零ホモトピーを選ぶ。 -/
def projectedNullHomotopy (n : ℕ) :
    PtSimplex.RelStruct .const (projectedSimplex X p r s n) (Fin.last (r + 1)) :=
  Classical.choice (exists_projected_nullHomotopy X p r s hzero n)

/-- 比較の核の固定した球面代表に付随する lim¹ の障害。 -/
def kernelRepresentativeObstruction :
    TowerLimOne.limOne (fun n ↦ KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n)) :=
  nullHomotopyObstruction X p r (projectedSimplex X p r s) (projectedSimplex_comp X p r s)
    (projectedNullHomotopy X p r s hzero)

/-- 核の代表の障害は、任意の段ごとの零ホモトピーから計算できる。 -/
lemma kernelRepresentativeObstruction_eq
    (R : ∀ n, PtSimplex.RelStruct .const (projectedSimplex X p r s n) (Fin.last (r + 1))) :
    kernelRepresentativeObstruction X p r s hzero =
      nullHomotopyObstruction X p r (projectedSimplex X p r s) (projectedSimplex_comp X p r s) R :=
  nullHomotopyObstruction_eq X p r _ _ _ R

include hzero in
/-- 整合する零ホモトピーを持つ核の代表の障害は基点になる。 -/
theorem kernelRepresentativeObstruction_eq_point_of_compatible
    (R : ∀ n, PtSimplex.RelStruct .const (projectedSimplex X p r s n) (Fin.last (r + 1)))
    (hc : ∀ n, (R (n + 1)).map ≫ (p n).right = (R n).map) :
    kernelRepresentativeObstruction X p r s hzero = TowerLimOne.point _ _ := by
  rw [kernelRepresentativeObstruction_eq X p r s hzero R]
  exact nullHomotopyObstruction_eq_point_of_compatible X p r _ _ R hc

/-- 極限での零ホモトピーを射影した場合、代表の障害は基点になる。 -/
theorem kernelRepresentativeObstruction_eq_point_of_null
    (R : PtSimplex.RelStruct .const s (Fin.last (r + 1))) :
    kernelRepresentativeObstruction X p r s hzero = TowerLimOne.point _ _ := by
  let R' n := NullHomotopyDifference.mapNull
    (FibrationTower.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n) rfl R
  apply kernelRepresentativeObstruction_eq_point_of_compatible X p r s hzero R'
  intro n
  change (R.map ≫ FibrationTower.projection _ _ (n + 1)) ≫ (p n).right =
    R.map ≫ FibrationTower.projection _ _ n
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kan.FibrationTower.projection_comp]

/-- 極限のホモトピー群で零となる代表は lim¹ の零障害を持つ。 -/
theorem kernelRepresentativeObstruction_eq_point_of_mk_eq_one
    (he : KanHomotopyGroup.mk s = 1) :
    kernelRepresentativeObstruction X p r s hzero = TowerLimOne.point _ _ := by
  obtain ⟨R⟩ := (simplexRel_iff_relStruct (Fin.last (r + 1))).1
    ((KanHomotopyGroup.mk_eq_iff .const s).1 he.symm)
  exact kernelRepresentativeObstruction_eq_point_of_null X p r s hzero R

end
end SerrePositivity.KST.Spectra.PointedFibrationTower

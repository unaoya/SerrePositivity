module

public import SerrePositivity.AlgebraicGeometry.OpenCoverCechResolution
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSplitExact
public import Mathlib.Order.CompleteLattice.Finset

/-!
概要：交叉全体を含む被覆の頂点がある場合の、切断の増大 Čech 完全性。
方針：その頂点の挿入で開集合の交叉が変わらないことから、既存の縮約を使う。
規約：前層について成立し、層性・準連接性・被覆性は仮定しない。
使われ方：二重 Čech の正次数の行を完全にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace
universe u v
variable {X : Type u} [TopologicalSpace X] {R : Type v} [CommRing R]
variable (P : (Opens X)ᵒᵖ ⥤ ModuleCat R) {ι : Type} [LinearOrder ι]
variable (W : Opens X) (U : ι → Opens X)

/-- 頂点の挿入に対応する開集合の交叉。 -/
theorem cechOpenIntersection_insert (v : ι) (T : Finset ι) :
    cechOpenIntersection U (insert v T) = U v ⊓ cechOpenIntersection U T := by
  simp only [cechOpenIntersection, ← Finset.inf_eq_iInf, Finset.inf_insert]

/-- 交叉全体を含む頂点の挿入による、切断の制限は同型。 -/
theorem openCoverCechSplitIntersection_isIso (v : ι) (h : W ≤ U v) :
    ∀ T, IsIso ((fullCechInsertVertexMap
      (openCoverCechDiagram (openCoverIntersectionPresheaf P W) U) v).app T) := by
  intro T
  have he : W ⊓ cechOpenIntersection U (insert v T) = W ⊓ cechOpenIntersection U T := by
    rw [cechOpenIntersection_insert, ← inf_assoc, inf_eq_left.mpr h]
  change IsIso (P.map (homOfLE (inf_le_inf le_rfl
    (cechOpenIntersection_antitone U (Finset.subset_insert v T)))).op)
  have hm : (homOfLE (inf_le_inf le_rfl
      (cechOpenIntersection_antitone U (Finset.subset_insert v T))) :
        W ⊓ cechOpenIntersection U (insert v T) ⟶ W ⊓ cechOpenIntersection U T) =
      eqToHom he := Subsingleton.elim _ _
  rw [hm]
  infer_instance

/-- 交叉全体を含む頂点がある場合、増大項の微分は単射。 -/
theorem openCoverCechSplitIntersection_zero_injective (v : ι) (h : W ≤ U v) :
    Function.Injective
      (fullCechDifferential (openCoverCechDiagram (openCoverIntersectionPresheaf P W) U) 0) := by
  letI := openCoverCechSplitIntersection_isIso P W U v h
  exact fullCechSplitVertexDifferential_zero_injective
    (openCoverCechDiagram (openCoverIntersectionPresheaf P W) U) v

/-- 交叉全体を含む頂点がある前層の増大 Čech の完全性。
原典 Stacks 30.2.1 の Hⁱ の計算に用いる Čech 版の縮約。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem openCoverCechSplitIntersection_exact (v : ι) (h : W ≤ U v) (k : ℕ) :
    Function.Exact
      (fullCechDifferential (openCoverCechDiagram (openCoverIntersectionPresheaf P W) U) k)
      (fullCechDifferential (openCoverCechDiagram (openCoverIntersectionPresheaf P W) U) (k + 1)) := by
  let D := openCoverCechDiagram (openCoverIntersectionPresheaf P W) U
  letI := openCoverCechSplitIntersection_isIso P W U v h
  intro x
  constructor
  · exact fullCechSplitVertex_cycle_boundary D v k x
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (fullCechAugmentedDifferential_squared D k) y

end SerrePositivity.AlgebraicGeometry

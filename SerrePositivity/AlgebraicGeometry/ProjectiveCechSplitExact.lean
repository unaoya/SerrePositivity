module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSplitVertex

/-!
概要：固定頂点による縮約から、増大項を含む全タプル Čech の完全性を得る。
方針：長さ零では鎖の先頭追加を直接計算し、正長では既存の縮約恒等式を使う。
規約：頂点挿入のすべての制限が同型であることを仮定する。
使われ方：共通アフィン細分の二重図式の、交叉全体を含む被覆元がある行。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι]

/-- 長さ零のタプルでは、先頭を追加して境界を取ると元に戻る。 -/
theorem cechTupleBoundary_prepend_zero (v : ι) :
    (cechTupleBoundary 0).comp (cechTuplePrepend v 0) =
      (LinearMap.id : CechTupleChains ι 0 →ₗ[ℤ] _) := by
  apply Finsupp.lhom_ext
  intro t c
  simp [cechTupleBoundary, cechTuplePrepend, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single, Fin.sum_univ_succ]

/-- 長さ零の先頭挿入と余境界の合成は、頂点挿入による係数の制限。 -/
theorem fullCechPrependVertex_zero_differential (D : Finset ι ⥤ ModuleCat R) (v : ι) :
    (fullCechPrependVertex D v 0).comp (fullCechDifferential D 0) =
      fullCechCochainsMap (fullCechInsertVertexMap D v) 0 := by
  rw [← fullCechInsertTranspose_prepend D v 0, ← fullCechTranspose_boundary D 0,
    ← fullCechInsertTranspose_comp_preserving_left D v _ _
      (cechTupleBoundary_preservesSupport 0) (cechTuplePrepend_support_insert v 0),
    cechTupleBoundary_prepend_zero, fullCechInsertTranspose_id]

/-- 全タプルの余境界の二乗は、長さ零の増大項からも零となる。 -/
theorem fullCechAugmentedDifferential_squared (D : Finset ι ⥤ ModuleCat R) (k : ℕ) :
    (fullCechDifferential D (k + 1)).comp (fullCechDifferential D k) = 0 := by
  have hd : (cechTupleBoundary (ι := ι) k).comp (cechTupleBoundary (k + 1)) = 0 := by
    apply LinearMap.ext
    exact cechTupleBoundary_squared k
  rw [← fullCechTranspose_boundary D (k + 1), ← fullCechTranspose_boundary D k,
    ← fullCechTranspose_comp D _ _ (cechTupleBoundary_preservesSupport k)
      (cechTupleBoundary_preservesSupport (k + 1)), hd]
  apply LinearMap.ext
  intro a
  funext t
  simp [fullCechTranspose]

variable (D : Finset ι ⥤ ModuleCat R) (v : ι)
variable [hInsert : ∀ T, IsIso ((fullCechInsertVertexMap D v).app T)]
include v hInsert

/-- 増大項での縮約も、余境界との合成が恒等になる。 -/
theorem fullCechSplitVertexContraction_zero_identity :
    (fullCechSplitVertexContraction D v 0).comp (fullCechDifferential D 0) = LinearMap.id := by
  let e := fullCechInsertVertexIso D v
  change ((fullCechCochainsMap e.inv 0).comp (fullCechPrependVertex D v 0)).comp _ = _
  rw [LinearMap.comp_assoc, fullCechPrependVertex_zero_differential]
  apply LinearMap.ext
  intro a
  funext t
  change (e.inv.app (cechTupleSupport t)).hom ((e.hom.app (cechTupleSupport t)).hom (a t)) = a t
  have he : e.hom.app (cechTupleSupport t) ≫ e.inv.app (cechTupleSupport t) = 𝟙 _ :=
    congrArg (fun η ↦ η.app (cechTupleSupport t)) e.hom_inv_id
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
    LinearMap.id_apply] using congrArg (fun f ↦ f.hom (a t)) he

/-- 固定頂点による縮約があれば、増大項からの余境界は単射。 -/
theorem fullCechSplitVertexDifferential_zero_injective :
    Function.Injective (fullCechDifferential D 0) := by
  have h : Function.LeftInverse (fullCechSplitVertexContraction D v 0)
      (fullCechDifferential D 0) :=
    fun a ↦ LinearMap.congr_fun (fullCechSplitVertexContraction_zero_identity D v) a
  exact h.injective

/-- 固定頂点による縮約があれば、正の長さの各 Čech サイクルは境界。 -/
theorem fullCechSplitVertex_cycle_boundary (k : ℕ) (a : FullCechCochains D (k + 1))
    (ha : fullCechDifferential D (k + 1) a = 0) :
    ∃ b, fullCechDifferential D k b = a := by
  refine ⟨fullCechSplitVertexContraction D v k a, ?_⟩
  have h := LinearMap.congr_fun (fullCechSplitVertexContraction_identity D v k) a
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, ha, map_zero, zero_add,
    LinearMap.id_apply] using h

end SerrePositivity.AlgebraicGeometry

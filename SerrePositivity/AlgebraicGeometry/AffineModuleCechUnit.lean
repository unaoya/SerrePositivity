module

public import SerrePositivity.AlgebraicGeometry.AffineModuleCechDiagram
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSplitExact

/-!
概要：被覆元の一つが単元なら、アフィン標準被覆の増大 Čech は完全。
方針：その頂点を挿入する制限の同型性を、一般の先頭挿入の縮約へ渡す。
規約：ここでは単位イデアルを生成する一般の場合とは区別し、一つが単元の場合を扱う。
使われ方：各被覆元で局所化した後のアフィン Čech の完全性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {A : Type u} [CommRing A] {ι : Type} [LinearOrder ι]
variable (M : Type u) [AddCommGroup M] [Module A M] (f : ι → A)

/-- 単元の頂点の挿入は、係数図式のすべての成分で同型。 -/
theorem affineModuleCechUnitInsertionIsIso (v : ι) (hv : IsUnit (f v)) :
    ∀ T, IsIso ((fullCechInsertVertexMap (affineModuleCechDiagram M f) v).app T) :=
  fun T ↦ affineModuleCechDiagram_map_insert_isIso M f v hv T

/-- 単元の被覆元があれば、増大項からの写像は単射。 -/
theorem affineModuleCechUnit_zero_injective (v : ι) (hv : IsUnit (f v)) :
    Function.Injective (fullCechDifferential (affineModuleCechDiagram M f) 0) := by
  letI := affineModuleCechUnitInsertionIsIso M f v hv
  exact fullCechSplitVertexDifferential_zero_injective (affineModuleCechDiagram M f) v

/-- 単元の被覆元があれば、増大 Čech の各サイクルは境界。
原典 Stacks 30.2.1 の Čech 消滅の証明で、局所化後に用いる単元の場合の加群計算。
層コホモロジーの Hⁱ との比較はこの補題には用いない。 -/
theorem affineModuleCechUnit_cycle_boundary (v : ι) (hv : IsUnit (f v))
    (k : ℕ) (x : FullCechCochains (affineModuleCechDiagram M f) (k + 1))
    (hx : fullCechDifferential (affineModuleCechDiagram M f) (k + 1) x = 0) :
    ∃ y, fullCechDifferential (affineModuleCechDiagram M f) k y = x := by
  letI := affineModuleCechUnitInsertionIsIso M f v hv
  exact fullCechSplitVertex_cycle_boundary (affineModuleCechDiagram M f) v k x hx

/-- 単元の被覆元があれば、増大 Čech の連続する二つの余境界は完全。 -/
theorem affineModuleCechUnit_exact (v : ι) (hv : IsUnit (f v)) (k : ℕ) :
    Function.Exact (fullCechDifferential (affineModuleCechDiagram M f) k)
      (fullCechDifferential (affineModuleCechDiagram M f) (k + 1)) := by
  intro x
  constructor
  · exact affineModuleCechUnit_cycle_boundary M f v hv k x
  · rintro ⟨y, rfl⟩
    exact LinearMap.congr_fun (fullCechAugmentedDifferential_squared (affineModuleCechDiagram M f) k) y

end SerrePositivity.AlgebraicGeometry

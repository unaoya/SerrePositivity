module
public import SerrePositivity.DifferentialGraded.Verdier.KernelActionTriangles

/-! # Perf 上の Morita 判定で使う一般 kernel 作用の三角性

実際の主導来作用を保持し、入力の射影的ホモトピー圏上の tensor 計算から得た
既存の shift・三角性を公開する。一般 kernel の右随伴は使わない。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (K : Kernel A D E)

/-- 一般 kernel の実際の作用に対する、tensor 計算由来の整数 shift 構造。 -/
@[instance_reducible]
def criterionPerfKernelCommShift : (kernelDerivedTensor A D E K).CommShift ℤ :=
  mainKernelActionCommShift A D E K

/-- 一般 kernel の主導来作用は完全三角形を保存する。平坦性条件は不要。 -/
lemma criterionPerfKernelIsTriangulated :
    letI := criterionPerfKernelCommShift A D E K
    (kernelDerivedTensor A D E K).IsTriangulated :=
  mainKernelActionIsTriangulated A D E K

/-- 完全三角形の保存を、選択した shift と実際の作用関手について明記する。 -/
lemma criterionPerfKernel_map_distinguished
    (Δ : Triangle (DerivedModuleCategory A D))
    (hΔ : Δ ∈ distTriang (DerivedModuleCategory A D)) :
    letI := criterionPerfKernelCommShift A D E K
    (kernelDerivedTensor A D E K).mapTriangle.obj Δ ∈ distTriang (DerivedModuleCategory A E) := by
  let := criterionPerfKernelCommShift A D E K
  let := criterionPerfKernelIsTriangulated A D E K
  exact (kernelDerivedTensor A D E K).map_distinguished Δ hΔ

variable (hK : kernelColumnsPerfect A D E K)

/-- 列の perfect 性だけを使う、実際の Perf 制限の整数 shift。 -/
@[instance_reducible]
def criterionPerfActionCommShift : (perfectDerivedKernelAction A D E K hK).CommShift ℤ :=
  mainPerfectKernelActionCommShift A D E K hK

lemma criterionPerfActionIsTriangulated :
    letI := criterionPerfActionCommShift A D E K hK
    (perfectDerivedKernelAction A D E K hK).IsTriangulated :=
  mainPerfectKernelActionIsTriangulated A D E K hK

/-- 第一条件の列の perfect 性は、実際の主作用が Perf を保つことと同値。 -/
lemma criterionPerfColumns_iff_preservesPerfect :
    kernelColumnsPerfect A D E K ↔
      ∀ X, modulePerfect A D X → modulePerfect A E ((kernelDerivedTensor A D E K).obj X) :=
  kernelColumnsPerfect_iff_preservesPerfect A D E K
end SerrePositivity.DifferentialGraded.Morita

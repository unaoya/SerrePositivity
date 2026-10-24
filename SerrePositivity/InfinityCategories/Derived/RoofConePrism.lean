module
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RightKanShapeCommaComparison
public import SerrePositivity.InfinityCategories.Core.Limit

/-! # 実 join 錐からの共通始点 prism

概要：指定された実錐から、共通頂点に定値の始端と元の図式の終端を持つ prism を取り出す。
方針：共通頂点の coslice へ curry し、その指定ホモトピーの時間を第一因子へ移す。
規約：入力の実錐と頂点を保つ。使われ方：右ファイブレーションの相対 fiber 還元。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
variable {K B : SSet.{u}} {f : K ⟶ B} (c : JoinCone f)

/-- 共通錐頂点から元の図式への実ホモトピー。 -/
def roofConeInitialHomotopy : SSet.Homotopy (SSet.const c.vertex) f := by
  have hl : joinInl (Δ[0] : SSet.{u}) K ≫ c.val = SSet.yonedaEquiv.symm c.vertex := by
    rw [JoinCone.vertex_eq, Equiv.symm_apply_apply]
  let a := sliceUnderCurry c.val hl
  have ha : a ≫ sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex) = f := by
    rw [← sliceUnderUncurry_projection, sliceUnderUncurry_curry]
    exact c.property
  exact Eq.mp (congrArg (fun g => SSet.Homotopy (SSet.const c.vertex) g) ha)
    (F1B.kanPointCosliceHomotopy c.vertex a)

/-- 実錐に付随する、時間を第一因子に置いた底の prism。 -/
def roofConePrism : (Δ[1] : SSet.{u}) ⊗ K ⟶ B :=
  (β_ (Δ[1] : SSet.{u}) K).hom ≫ (roofConeInitialHomotopy c).h

/-- 底 prism の始端は指定された共通錐頂点に定値。 -/
lemma roofConePrism_zero : prismEndpoint 0 K ≫ roofConePrism c = SSet.const c.vertex := by
  change prismEndpoint 0 K ≫ ((β_ Δ[1] K).hom ≫ _) = _
  rw [← Category.assoc, prismEndpoint_zero_braiding]
  exact (roofConeInitialHomotopy c).h₀

/-- 底 prism の終端は元の図式と厳密に一致する。 -/
lemma roofConePrism_one : prismEndpoint 1 K ≫ roofConePrism c = f := by
  change prismEndpoint 1 K ≫ ((β_ Δ[1] K).hom ≫ _) = _
  rw [← Category.assoc, prismEndpoint_one_braiding]
  exact (roofConeInitialHomotopy c).h₁

end SerrePositivity.InfinityCategories

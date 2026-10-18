module

public import SerrePositivity.KST.Comparison.FatSkeletonMaps
public import SerrePositivity.KST.Comparison.FatBoundaryCriterion
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# 新しい行の境界の有限骨格への付着

概要：n+1 行の境界の積を n 骨格へ送り、その厳密な引き戻しの四角形を証明する。
方針：標準形の像の次元と非全射性の同値を使い、部分型の普遍性を各次数で確認する。
規約：Segal 1974 Proposition 1.6 の有限骨格の付着。
使われ方：型の pushout 判定による一段階の骨格の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory
open scoped Simplicial

/--
概要：有限骨格の一段階の包含。
方針：次元による部分単体集合の包含を使う。
規約：第 n 項から第 n+1 項へ向く。
使われ方：一段階の付着の pushout の射。
-/
def fatSkeletonStep (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    (fatSkeleton F n : SSet.{u}) ⟶ (fatSkeleton F (n + 1) : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (fatSkeleton_monotone F (Nat.le_succ n))

/--
概要：一段階の包含は全体への包含と可換である。
方針：部分単体集合の包含の定義を使う。
規約：旧骨格の元を変えない等式。
使われ方：付着の図式の全体への比較。
-/
@[reassoc] theorem fatSkeletonStep_ι (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    fatSkeletonStep F n ≫ (fatSkeleton F (n + 1)).ι = (fatSkeleton F n).ι := rfl

/--
概要：n+1 行の境界との積から n 骨格への付着写像。
方針：境界に属することと旧骨格へ入ることの同値で、包含を部分単体集合へ持ち上げる。
規約：境界は Mathlib の標準単体の境界。
使われ方：一段階の付着の pushout の第一の脚。
-/
def fatBoundaryAttachment (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    F.obj (op ⦋n + 1⦌) ⊗ (SSet.boundary (n + 1) : SSet.{u}) ⟶ (fatSkeleton F n : SSet.{u}) :=
  SSet.Subcomplex.lift ((F.obj (op ⦋n + 1⦌) ◁ (SSet.boundary (n + 1)).ι) ≫
    fatRealizationInclusion F (n + 1)) (by
      rintro d y ⟨⟨x, t⟩, rfl⟩
      exact (fatRealizationInclusion_mem_skeleton_iff_boundary F n d x t.1).mpr t.2)

/--
概要：境界の付着を全体へ含めると、行の包含の境界への制限になる。
方針：部分単体集合への lift の計算則を使う。
規約：境界との積の射と全体の行の包含を合成する向き。
使われ方：付着の四角形の可換性。
-/
@[reassoc] theorem fatBoundaryAttachment_ι (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    fatBoundaryAttachment F n ≫ (fatSkeleton F n).ι =
      (F.obj (op ⦋n + 1⦌) ◁ (SSet.boundary (n + 1)).ι) ≫
        fatRealizationInclusion F (n + 1) := rfl

/--
概要：新しい行の境界との積は、旧骨格の全体への包含の厳密な引き戻しである。
方針：各次数で、旧骨格に入る行の元が境界に属することから一意な持ち上げを作る。
規約：ホモトピー引き戻しの主張ではなく、実際の普遍性。
使われ方：一段階の骨格の付着の pushout 判定。
-/
theorem fatBoundaryAttachment_isPullback (F : SimplexCategoryᵒᵖ ⥤ SSet.{u}) (n : ℕ) :
    IsPullback (fatBoundaryAttachment F n)
      (F.obj (op ⦋n + 1⦌) ◁ (SSet.boundary (n + 1)).ι)
      (fatSkeleton F n).ι (fatRealizationInclusion F (n + 1)) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · rintro ⟨x, t⟩ ⟨y, u⟩ ⟨_, h⟩
    change (x, t.1) = (y, u.1) at h
    exact Prod.ext
      (congrArg (fun p : (F.obj (op ⦋n + 1⦌)).obj d × Δ[n + 1].obj d => p.1) h)
      (Subtype.ext (congrArg (fun p : (F.obj (op ⦋n + 1⦌)).obj d × Δ[n + 1].obj d => p.2) h))
  · rintro s ⟨x, t⟩ h
    change s.1 = (fatRealizationInclusion F (n + 1)).app d (x, t) at h
    have ht : t ∈ (SSet.boundary (n + 1)).obj d :=
      (fatRealizationInclusion_mem_skeleton_iff_boundary F n d x t).mp (h ▸ s.2)
    refine ⟨(x, ⟨t, ht⟩), ?_, rfl⟩
    apply Subtype.ext
    exact h.symm

end SerrePositivity.KST.Comparison

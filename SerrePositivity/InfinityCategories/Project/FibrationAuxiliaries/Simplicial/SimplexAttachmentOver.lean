module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CellAttachmentFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
概要：任意の底上で、標準単体を指定した境界に沿って既存部分へ貼る。
方針：底上の圏で pushout を取り、忘却関手で同じ基礎の pushout を回収する。
規約：境界の貼付け写像の単射性や既存部分の quasicategory 性を要求しない。
使われ方：有限セルと骨格の段階の元の Hom の制限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial
namespace SimplexAttachmentOver

variable {B : SSet.{u}} (n : ℕ) (σ : (Δ[n] : SSet.{u}) ⟶ B)

/-- 底の同じ単体の境界。 -/
def boundary : Over B := Over.mk ((SSet.boundary n).ι ≫ σ)

/-- 付加する元の標準単体。 -/
def cell : Over B := Over.mk σ

/-- 元の標準単体への同じ境界包含。 -/
def boundaryInclusion : boundary n σ ⟶ cell n σ := Over.homMk (SSet.boundary n).ι rfl

instance : Mono (boundaryInclusion n σ).left := inferInstanceAs (Mono (SSet.boundary n).ι)

variable {c : Over B} (u : boundary n σ ⟶ c)

/-- 指定された底上の境界の貼付けによる、元の既存部分へのセル付加。 -/
def apex : Over B := pushout (boundaryInclusion n σ) u

/-- 付加した標準単体から全体への元の射。 -/
def cellInclusion : cell n σ ⟶ apex n σ u := pushout.inl _ _

/-- 既存部分から全体への元の射。 -/
def oldInclusion : c ⟶ apex n σ u := pushout.inr _ _

/-- 底上で構成した同じセル付加は、基礎の単体集合でも pushout。 -/
lemma isPushout : IsPushout (boundaryInclusion n σ).left u.left
    (cellInclusion n σ u).left (oldInclusion n σ u).left :=
  (IsPushout.of_hasPushout (boundaryInclusion n σ) u).map (Over.forget B)

instance : Mono (oldInclusion n σ u).left :=
  Adhesive.mono_of_isPushout_of_mono_left (isPushout n σ u)

end SimplexAttachmentOver
end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Simplicial

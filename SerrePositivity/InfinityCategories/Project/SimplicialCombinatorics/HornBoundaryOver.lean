module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryPushout
public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
概要：任意の底上の標準境界を、同じホーンと欠けた面の pushout に束ねる。
方針：四つの標準包含の式を元の単体写像へ後合成する。
規約：底も境界も quasicategory である必要はない。
使われ方：同じ境界の native Hom と分類先 Hom の相対比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
namespace HornBoundaryOver
variable {B : SSet.{u}} (n : ℕ) (i : Fin (n + 2)) (σ : (Δ[n + 1] : SSet.{u}) ⟶ B)

/-- 元の同じ単体の境界全体。 -/
def apex : Over B := Over.mk ((boundary (n + 1)).ι ≫ σ)

/-- 同じ標準ホーン。 -/
def horn : Over B := Over.mk ((SSet.horn (n + 1) i).ι ≫ σ)

/-- 欠けている同じ標準面。 -/
def face : Over B := Over.mk (stdSimplex.δ i ≫ σ)

/-- 欠けた標準面の同じ境界。 -/
def shared : Over B := Over.mk ((boundary n).ι ≫ stdSimplex.δ i ≫ σ)

/-- 共有境界から付加する面への標準包含。 -/
def toFace : shared n i σ ⟶ face n i σ := Over.homMk (boundary n).ι rfl

/-- 共有境界から同じホーンへの標準包含。 -/
def toHorn : shared n i σ ⟶ horn n i σ :=
  Over.homMk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryToHorn n i) (by
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryToHorn n i ≫ ((SSet.horn (n + 1) i).ι ≫ σ) = _
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryToHorn_ι, Category.assoc]
    rfl)

/-- 同じ面から標準境界全体への包含。 -/
def faceInclusion : face n i σ ⟶ apex n σ :=
  Over.homMk (boundary.ι i) (by
    change boundary.ι i ≫ ((boundary (n + 1)).ι ≫ σ) = _
    rw [← Category.assoc, boundary.ι_ι]
    rfl)

/-- 同じホーンから標準境界全体への包含。 -/
def hornInclusion : horn n i σ ⟶ apex n σ :=
  Over.homMk (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion n i) (by
    change _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryInclusion n i ≫ ((boundary (n + 1)).ι ≫ σ) = _
    rw [← Category.assoc]
    rfl)

/-- 付加する面を第一の枝とする、同じ底上の四射の基礎の pushout。 -/
lemma isPushout : IsPushout (toFace n i σ).left (toHorn n i σ).left
    (faceInclusion n i σ).left (hornInclusion n i σ).left :=
  (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryAttachment_isPushout n i).flip

instance : Mono (toFace n i σ).left := inferInstanceAs (Mono (boundary n).ι)

instance : Mono (toHorn n i σ).left :=
  mono_of_mono_fac (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornMissingFaceBoundaryToHorn_ι n i)

instance : Mono (faceInclusion n i σ).left := inferInstanceAs (Mono (boundary.ι i))

instance : Mono (hornInclusion n i σ).left :=
  inferInstanceAs (Mono (Subcomplex.homOfLE (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.hornBoundaryBicartSq n i).le₂₄))

end HornBoundaryOver
end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

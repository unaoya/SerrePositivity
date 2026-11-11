module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeFamily
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
/-!
概要：κ 未満 sphere-free 表示のラベルに dg 関手を厳密に作用させる。
方針：ordinal と次数を保持し、縮小した対象ラベルだけを元の対象作用で写す。
規約：対象ラベルの恒等・合成を等式で証明する。Hom 作用と cone 閉性は別工程。
使われ方：16時間試作の小さい表示型と、全次数作用を束ねる際の対象部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R]
variable {D : Type v} {E : Type w} {B : Type z}
  [DGCategory R D] [DGCategory R E] [DGCategory R B]
  [Small.{u} D] [Small.{u} E] [Small.{u} B]

/-- 同じ ordinal と次数を持つ表示へ、実対象ラベルを写す。 -/
def dgKappaSphereFreeLabelMap {κ : Cardinal.{u}} (F : DGFunctor R D E)
    (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex E κ :=
  ⟨i.1, fun j => (equivShrink E (F.obj ((equivShrink D).symm (i.2 j).1)), (i.2 j).2)⟩

lemma dgKappaSphereFreeLabelMap_id {κ : Cardinal.{u}}
    (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) :
    dgKappaSphereFreeLabelMap R (DGFunctor.id D) i = i := by
  rcases i with ⟨a, s⟩
  apply congrArg (fun f : Set.Iio a → Shrink.{u} D × ℤ =>
    (⟨a, f⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ))
  funext j
  apply Prod.ext
  · exact Equiv.apply_symm_apply _ _
  · rfl

lemma dgKappaSphereFreeLabelMap_comp {κ : Cardinal.{u}}
    (F : DGFunctor R D E) (G : DGFunctor R E B) (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) :
    dgKappaSphereFreeLabelMap R (F.comp G) i =
      dgKappaSphereFreeLabelMap R G (dgKappaSphereFreeLabelMap R F i) := by
  rcases i with ⟨a, s⟩
  apply congrArg (fun f : Set.Iio a → Shrink.{u} B × ℤ =>
    (⟨a, f⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex B κ))
  funext j
  apply Prod.ext
  · dsimp only [dgKappaSphereFreeLabelMap, DGFunctor.comp, EnrichedFunctor.comp]
    rw [Equiv.symm_apply_apply]
  · rfl

lemma dgKappaSphereFreeLabelMap_ordinal {κ : Cardinal.{u}}
    (F : DGFunctor R D E) (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) :
    (dgKappaSphereFreeLabelMap R F i).1 = i.1 := rfl

lemma dgKappaSphereFreeLabelMap_object {κ : Cardinal.{u}}
    (F : DGFunctor R D E) (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) (j : Set.Iio i.1) :
    (equivShrink E).symm ((dgKappaSphereFreeLabelMap R F i).2 j).1 =
      F.obj ((equivShrink D).symm (i.2 j).1) :=
  Equiv.symm_apply_apply _ _

lemma dgKappaSphereFreeLabelMap_degree {κ : Cardinal.{u}}
    (F : DGFunctor R D E) (i : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ) (j : Set.Iio i.1) :
    ((dgKappaSphereFreeLabelMap R F i).2 j).2 = (i.2 j).2 := rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories

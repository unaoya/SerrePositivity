module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceModel
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeZero
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaClosedProjectiveOperations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorConeComponents
/-!
概要：空の出発提示とその零 seed により、厳密に保存される零ラベルを構成する。
方針：κ の空初期区間の提示から唯一の dg 関手を作り、既存の零加群閉包を評価する。
規約：標的 dg 圏の非空性を要求せず、後合成によって零ラベルを再選択しない。
使われ方：16時間試作の同じ出発提示模型の零対象と前三角性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 < κ)

def dgKappaEmptyCategoryCode : DGCategoryPresentationCode R κ where
  ordinal := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaFreeEmptyOrdinal (lt_trans Cardinal.aleph0_pos hκ)
  hom x _ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaFreeEmptyEquiv (lt_trans Cardinal.aleph0_pos hκ) x).elim
  unit x := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaFreeEmptyEquiv (lt_trans Cardinal.aleph0_pos hκ) x).elim
  comp x _ _ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaFreeEmptyEquiv (lt_trans Cardinal.aleph0_pos hκ) x).elim
  left x _ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaFreeEmptyEquiv (lt_trans Cardinal.aleph0_pos hκ) x).elim
  right x _ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaFreeEmptyEquiv (lt_trans Cardinal.aleph0_pos hκ) x).elim
  assoc x _ _ _ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaFreeEmptyEquiv (lt_trans Cardinal.aleph0_pos hκ) x).elim

instance dgKappaEmptyCategoryCode_isEmpty :
    IsEmpty ((dgKappaEmptyCategoryCode R κ hκ).Objects R κ) :=
  ⟨fun x => (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaFreeEmptyEquiv (lt_trans Cardinal.aleph0_pos hκ) x).elim⟩

variable (D : Type u) [DGCategory R D]

def dgKappaEmptyCategoryFunctor :
    DGFunctor R ((dgKappaEmptyCategoryCode R κ hκ).Objects R κ) D where
  obj x := isEmptyElim x
  map x _ := isEmptyElim x
  map_id x := isEmptyElim x
  map_comp x _ _ := isEmptyElim x

def dgKappaPresentedSourceZero : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ where
  code := dgKappaEmptyCategoryCode R κ hκ
  seed := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_zero R
    ((dgKappaEmptyCategoryCode R κ hκ).Objects R κ) hκ).choose
  arrow := dgKappaEmptyCategoryFunctor R κ hκ D

lemma dgKappaPresentedSourceZero_seed :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceSeed R D κ (dgKappaPresentedSourceZero R κ hκ D) =
      moduleZero R ((dgKappaEmptyCategoryCode R κ hκ).Objects R κ) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceSeed _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSeedAt dgKappaPresentedSourceZero
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveObjects_zero R
    ((dgKappaEmptyCategoryCode R κ hκ).Objects R κ) hκ).choose_spec

lemma dgKappaPresentedSourceObjectMap_zero (E : Type u) [DGCategory R E]
    (F : DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceObjectMap R D κ E F (dgKappaPresentedSourceZero R κ hκ D) =
      dgKappaPresentedSourceZero R κ hκ E := by
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject.mk _ _
    ((dgKappaEmptyCategoryFunctor R κ hκ D).comp F) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject.mk _ _ (dgKappaEmptyCategoryFunctor R κ hκ E)
  apply congrArg (fun H => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject.mk _ _ H)
  apply EnrichedFunctor.ext (Complex R) (fun x => isEmptyElim x)
  intro x y
  exact isEmptyElim x

lemma dgKappaPresentedSourceZero_isZero :
    IsZero (ForgetEnrichment.of (Complex R)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceValue R D κ (dgKappaPresentedSourceZero R κ hκ D))) := by
  change IsZero ((dgModuleExtension R ((dgKappaEmptyCategoryCode R κ hκ).Objects R κ) D
    (dgKappaEmptyCategoryFunctor R κ hκ D)).onClosed.obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceSeed R D κ (dgKappaPresentedSourceZero R κ hκ D)))
  rw [dgKappaPresentedSourceZero_seed]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctor_zero_isZero R ((dgKappaEmptyCategoryCode R κ hκ).Objects R κ) D _

end SerrePositivity.InfinityCategories.Project.DerivedCategories

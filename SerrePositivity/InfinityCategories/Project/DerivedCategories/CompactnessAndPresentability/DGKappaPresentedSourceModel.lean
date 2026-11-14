module
public import SerrePositivity.DifferentialGraded.Presentation.Category
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaClosedProjectiveFamily
public import SerrePositivity.DifferentialGraded.Derived.FunctorExtensionAdjunction
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorCoherence
/-!
概要：小さい出発圏の提示・射影的 seed・延長関手をラベルに保持する模型を構成する。
方針：提示コードを Type u に固定し、評価後も出発圏と seed を選び直さない。
規約：現在は対象を u 宇宙に置く。全閉演算・被覆・κ-compact 性は別に検証する。
使われ方：16時間試作で入力の後合成と厳密に両立する小さい表示模型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded _root_.SerrePositivity.KST.SConstruction
variable (R : Type u) [CommRing R] (D : Type u) [DGCategory R D] (κ : Cardinal.{u})

structure DGKappaPresentedSourceObject where
  code : DGCategoryPresentationCode R κ
  seed : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (code.Objects R κ) κ).1
  arrow : DGFunctor R (code.Objects R κ) D

lemma dgKappaPresentedSourceObject_small : Small.{u} (DGKappaPresentedSourceObject R D κ) :=
  inferInstance

/-- seed の実値は出発提示と添字だけに依存する。 -/
@[irreducible] def dgKappaPresentedSeedAt (c : DGCategoryPresentationCode R κ)
    (i : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).1) :
    ModuleCategory R (c.Objects R κ) :=
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (c.Objects R κ) κ).2 i).val

def dgKappaPresentedSourceSeed (X : DGKappaPresentedSourceObject R D κ) :
    ModuleCategory R (X.code.Objects R κ) :=
  dgKappaPresentedSeedAt R κ X.code X.seed

def dgKappaPresentedSourceValue (X : DGKappaPresentedSourceObject R D κ) : RightModule R D :=
  (dgModuleExtension R (X.code.Objects R κ) D X.arrow).obj
    (ForgetEnrichment.to (Complex R) (dgKappaPresentedSourceSeed R D κ X))

lemma dgKappaPresentedSourceValue_projective (X : DGKappaPresentedSourceObject R D κ) :
    moduleHomotopicallyProjective R D
      (ForgetEnrichment.of (Complex R) (dgKappaPresentedSourceValue R D κ X)) :=
  dgModuleExtension_homotopicallyProjective R (X.code.Objects R κ) D X.arrow
    (P := dgKappaPresentedSourceSeed R D κ X) (by
      unfold dgKappaPresentedSourceSeed dgKappaPresentedSeedAt
      exact ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaClosedProjectiveFamily R (X.code.Objects R κ) κ).2 X.seed).property)

instance dgKappaPresentedSourceEnrichment : DGCategory R (DGKappaPresentedSourceObject R D κ) :=
  inducedDGCategory R (dgKappaPresentedSourceValue R D κ)

def dgKappaPresentedSourceEvaluation :
    DGFunctor R (DGKappaPresentedSourceObject R D κ) (RightModule R D) :=
  inducedDGEvaluation R (dgKappaPresentedSourceValue R D κ)

variable (E : Type u) [DGCategory R E] (F : DGFunctor R D E)

def dgKappaPresentedSourceObjectMap (X : DGKappaPresentedSourceObject R D κ) :
    DGKappaPresentedSourceObject R E κ where
  code := X.code
  seed := X.seed
  arrow := X.arrow.comp F

lemma dgKappaPresentedSourceObjectMap_id (X : DGKappaPresentedSourceObject R D κ) :
    dgKappaPresentedSourceObjectMap R D κ D (DGFunctor.id D) X = X := by
  rcases X with ⟨c, i, L⟩
  change DGKappaPresentedSourceObject.mk c i (L.comp (DGFunctor.id D)) =
    DGKappaPresentedSourceObject.mk c i L
  rw [strictDGFunctor_comp_id]

variable (B : Type u) [DGCategory R B] (G : DGFunctor R E B)
lemma dgKappaPresentedSourceObjectMap_comp (X : DGKappaPresentedSourceObject R D κ) :
    dgKappaPresentedSourceObjectMap R D κ B (F.comp G) X =
      dgKappaPresentedSourceObjectMap R E κ B G (dgKappaPresentedSourceObjectMap R D κ E F X) := by
  rcases X with ⟨c, i, L⟩
  change DGKappaPresentedSourceObject.mk c i (L.comp (F.comp G)) =
    DGKappaPresentedSourceObject.mk c i ((L.comp F).comp G)
  rw [strictDGFunctor_comp_assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories

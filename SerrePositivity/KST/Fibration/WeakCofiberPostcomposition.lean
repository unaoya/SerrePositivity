module
public import SerrePositivity.KST.Fibration.KernelPostcomposition
public import SerrePositivity.KST.Fibration.WeakStringCofiberFamilies
public import SerrePositivity.KST.SConstruction.RelativeEvaluationNaturality
public import SerrePositivity.KST.SConstruction.DoubleCofiberGrid

/-! # 元の完全関手による全相対 W cofiber 図式の後合成 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 元の W cofiber の相対入力。始点は全対象、cofiber は同じ商の核。 -/
def weakRelativeInput {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) : RelativeStableModel.{u} :=
  ⟨sInputModel B, ClosedStablePredicate.top (sInputModel B), kernelClosedPredicate q⟩

/-- 元の完全関手は、同じ核条件を保つ相対 cofiber 入力の射である。 -/
def weakRelativeInputMap {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakRelativeInput (f ≫ q : A ⟶ C) ⟶ weakRelativeInput q :=
  ⟨sInputExactMap f, ⟨fun _ _ => trivial, fun _ hx => hx⟩⟩

/-- 元の全相対 W cofiber 図式を、元の完全関手そのもので後合成する。 -/
def weakCofiberPostExact {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakCofiberModel (f ≫ q : A ⟶ C) ⟶ weakCofiberModel q :=
  relativeCofiberMap (weakRelativeInputMap f q)

/-- 相対 cofiber 後合成の quotient は、元の核への後合成と厳密に可換。 -/
lemma weakCofiberPostExact_quotient {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    weakCofiberPostExact f q ≫ relativeCofiberQuotient
      (ClosedStablePredicate.top (sInputModel B)) (kernelClosedPredicate q) =
        relativeCofiberQuotient (ClosedStablePredicate.top (sInputModel A))
          (kernelClosedPredicate (f ≫ q : A ⟶ C)) ≫ kernelPostExact f q :=
  relativeCofiberQuotient_naturality (weakRelativeInputMap f q)

/-- 相対 cofiber 後合成は、元の実底辺を全関手圏で厳密に後合成する。 -/
lemma weakCofiberPostExact_projection {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    (weakCofiberPostExact f q).val ≫
      (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q)).val ≫ cofiberProjection B.obj =
      (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel A))
        (kernelClosedPredicate (f ≫ q : A ⟶ C))).val ≫
          cofiberProjection A.obj ≫ (ihom (Δ[1] : SSet.{u})).map f.hom := by
  have he : (weakCofiberPostExact f q).val ≫
      (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel B))
        (kernelClosedPredicate q)).val =
      (relativeCofiberInclusion (ClosedStablePredicate.top (sInputModel A))
        (kernelClosedPredicate (f ≫ q : A ⟶ C))).val ≫
          cofiberPostcomp f.hom (sInputExactMap f).property :=
    congrArg Subtype.val (relativeCofiberMap_inclusion (weakRelativeInputMap f q))
  rw [← Category.assoc, he, Category.assoc]
  exact congrArg (fun g => (relativeCofiberInclusion
    (ClosedStablePredicate.top (sInputModel A))
      (kernelClosedPredicate (f ≫ q : A ⟶ C))).val ≫ g)
    (cofiberPostcomp_projection f.hom (sInputExactMap f).property)

end SerrePositivity.KST.Fibration

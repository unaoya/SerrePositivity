module
public import SerrePositivity.KST.Fibration.CofiberFamilyUntranspose

/-! # 商で零となる cofiber 族の相対図式への制限

関手圏の角の商像の零性を各パラメーターの元の角へ移す。
subobject と quotient が核に入る全四角形を E(ker q,B,ker q) に持ち上げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 関手圏の角の商像の零性から、復元した元の各角の核所属が従う。 -/
lemma cofiberFamilyUntranspose_corner_kernel {A : SSet.{u}} {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle ((ihom A).obj B.obj)) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (a : (Δ[1] ⊗ Δ[1] : SSet.{u}) _⦋0⦌)
    (hz : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom A).map q.hom).app (Opposite.op ⦋0⦌)
      (t.square.app (Opposite.op ⦋0⦌) a))) (v : A _⦋0⦌) :
    (kernelClosedPredicate q).predicate ((cofiberStableEvaluation (sInputModel B) a).val.app
      (Opposite.op ⦋0⦌) ((cofiberFamilyUntranspose t ht).app (Opposite.op ⦋0⦌) v)) := by
  let w := t.square.app (Opposite.op ⦋0⦌) a
  let F := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A B.obj).symm w
  have hw : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F = w := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A B.obj).apply_symm_apply w
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom A).map q.hom).app (Opposite.op ⦋0⦌) w) at hz
  rw [← hw] at hz
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ q.hom)) at hz
  have hp := isZeroVertex_evaluateFunctorAt hz v
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex] at hp
  have he := ConcreteCategory.congr_hom (NatTrans.congr_app
    (cofiberFamilyUntranspose_corner t ht a) (Opposite.op ⦋0⦌)) v
  exact (congrArg (fun x => _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) x)) he).mpr hp

/-- 両端が族として核に入る cofiber 列を、元の全相対四角形へ持ち上げる。 -/
def cofiberFamilyKernelRestriction {A : SSet.{u}} {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle ((ihom A).obj B.obj)) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom A).map q.hom).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom A).map q.hom).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1))) :
    A ⟶ relativeCofiberDiagrams (kernelClosedPredicate q) (kernelClosedPredicate q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (cofiberFamilyUntranspose t ht) (fun v =>
    ⟨cofiberFamilyUntranspose_corner_kernel q t ht _ h₀ v,
      cofiberFamilyUntranspose_corner_kernel q t ht _ h₁ v⟩)

/-- 相対制限の包含は、元の全 cofiber 図式の族を厳密に回収する。 -/
lemma cofiberFamilyKernelRestriction_ι {A : SSet.{u}} {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle ((ihom A).obj B.obj)) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom A).map q.hom).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 0 0)))
    (h₁ : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (((ihom A).map q.hom).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex t.square 1 1))) :
    cofiberFamilyKernelRestriction q t ht h₀ h₁ ≫
      (relativeCofiberInclusion (kernelClosedPredicate q) (kernelClosedPredicate q)).val =
        cofiberFamilyUntranspose t ht := rfl

end SerrePositivity.KST.Fibration

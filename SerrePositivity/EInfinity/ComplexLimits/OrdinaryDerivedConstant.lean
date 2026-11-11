module
public import SerrePositivity.EInfinity.FrameHom.MixedNerveConstant
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource

/-!
概要：元の通常複体の定値図式の導来化を同じ頂点の定値図式に照合する。
方針：混合宇宙の定値 nerve の等式と元の後合成を使う。
規約：元の図式と指定した頂点を保つ。使われ方：大域実屋根の両端の輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (I : Type (u + 1)) [Category.{u} I]

lemma complexOrdinaryDerivedConstant_eq (X : Complex A) :
    nerveMap ((Functor.const I).obj X) ≫ complexOrdinaryDerivedSource A =
    SSet.const ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)) := by
  rw [FrameHom.MixedNerve.nerveMap_const, SSet.const_comp]

def complexOrdinaryDerivedConstantIso (X : Complex A) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap ((Functor.const I).obj X) ≫ complexOrdinaryDerivedSource A)
      (SSet.const ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))) :=
  eqToIso (congrArg (fun f => HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f))
    (complexOrdinaryDerivedConstant_eq A I X))

end SerrePositivity.EInfinity.ComplexLimits

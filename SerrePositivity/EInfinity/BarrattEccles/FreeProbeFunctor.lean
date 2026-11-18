module

public import SerrePositivity.EInfinity.BarrattEccles.Fibrancy
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.FramedLimitProbeFunctor
public import SerrePositivity.HomotopicalAlgebra.Quillen.CofibrantObjects
public import SerrePositivity.HomotopicalAlgebra.Quillen.Brown

/-!
# 同じ複体の試験始域の実自由 E 代数

概要：元の複体の cofibrant probe の自由代数は cofibrant で、元の擬同型を保つ。
方針：実自由忘却随伴と右 Quillen U から左 Quillen 性を得て Brown を使う。
規約：元の複体に cofibrancy・標数の仮定を付けない。
使われ方：同じ U の導来 Hom 随伴比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]

lemma free_isLeftQuillen :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    let := modelCategory A
    SerrePositivity.Quillen.IsLeftQuillen (operad A).freeAlgebraFunctor := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := modelCategory A
  have := forget_isRightQuillen A
  exact SerrePositivity.Quillen.isLeftQuillen_of_isRightQuillen (operad A).freeAlgebraAdjunction

def freeProbeFunctor : Complex A ⥤ (operad A).Algebra :=
  _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A ⋙ (operad A).freeAlgebraFunctor

lemma freeProbeFunctor_cofibrant (X : Complex A) :
    let := modelCategory A
    IsCofibrant ((freeProbeFunctor A).obj X) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := modelCategory A
  have := free_isLeftQuillen A
  have := (operad A).freeAlgebraAdjunction.isLeftAdjoint
  have : IsCofibrant ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) :=
    _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A X
  exact SerrePositivity.Quillen.isCofibrant_obj (operad A).freeAlgebraFunctor _

lemma freeProbeFunctor_map_quasiIso {X Y : Complex A} (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso ((freeProbeFunctor A).map f).hom := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  let := modelCategory A
  have := free_isLeftQuillen A
  have : IsCofibrant ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj X) :=
    _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A X
  have : IsCofibrant ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).obj Y) :=
    _root_.SerrePositivity.ComplexLimits.framedLimitProbe_cofibrant A Y
  have h := _root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor_map_quasiIso A f hf
  have : WeakEquivalence ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).map f) := ⟨h⟩
  have hw := SerrePositivity.Quillen.map_weakEquivalence_of_cofibrant
    (operad A).freeAlgebraFunctor ((_root_.SerrePositivity.ComplexLimits.framedLimitProbeFunctor A).map f)
  exact (weakEquivalence_iff A _).mp hw

end SerrePositivity.EInfinity.BarrattEccles

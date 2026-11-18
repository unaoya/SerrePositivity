module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageFreeGenerators
public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseAttachmentGenerators
public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageWordEvaluation
public import SerrePositivity.EInfinity.BarrattEccles.Theory.SphereCoproductInclusions

/-!
# 自由表示の生成元と実際の付加生成元

## 概要
Berger–Moerdijk 命題 4.1 のセル段で、自由表示の生成元は実際の付加生成元の像である。

## 方針
自由・忘却随伴で指定された球の射を評価し、disk の下の生成元の像と比較する。

## 規約
比較は元のセル段の各次数の元の等式である。

## 使われ方
生成元の微分を実際の付加の境界で計算する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra DifferentialGraded
open MonoidalCategory
variable {A : Type u} [CommRing A]

/-- The sphere's own-degree basis vector is its specified unit generator. -/
lemma sphereDegreeBasis_self_apply (d : ℤ) (z : sphereDegreeIndex.{u} d d) :
    sphereDegreeBasis A d d z =
      (singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat A))).inv (1 : A) := by
  let b := (Module.Basis.singleton (ULift.{u} PUnit.{1}) A).map
    (singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat A))).symm.toLinearEquiv
  have ht (I : Type u) (h : ULift.{u} PUnit.{1} = I) (x : I) :
      (cast (congrArg (fun I : Type u => Module.Basis I A ((complexSphere A d).X d)) h) b) x =
        (singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat A))).inv (1 : A) := by
    subst I
    change b x = _
    rw [Module.Basis.map_apply, Module.Basis.singleton_apply]
    rfl
  have hi : ULift.{u} PUnit.{1} = sphereDegreeIndex.{u} d d := by
    simp [sphereDegreeIndex]
  simp only [sphereDegreeBasis]
  simp only [sphereDegreeIndex, dite_true, id_eq]
  exact ht _ hi z

namespace Operad
variable {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : P.Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => P.freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- Evaluating the specified sphere leg gives the attached generator in the later stage. -/
lemma cellStageGeneratorLeg_value (j : J) (x : CellsBefore (CellsAt c) j) :
    (P.erase.freeAlgebraAdjunction.homEquiv _ _
      (cellStageLeg (c.F ⋙ P.eraseAlgebra) (CellsAt c)
        (fun k y => P.erase.freeAlgebraFunctor.obj (cellSphere c k y))
        (cellGeneratorLeg c) j x)).f (cellDegree c x.1 x.2)
      ((singleObjXSelf (.up ℤ) (cellDegree c x.1 x.2)
        (𝟙_ (ModuleCat A))).inv (1 : A)) =
      (c.F.map (homOfLE (Order.succ_le_of_lt x.1.property))).hom.f (cellDegree c x.1 x.2)
        (attachedGenerator (c.attachCells x.1 x.2.1.down) x.2.2) := by
  change (P.erase.freeAlgebraAdjunction.homEquiv _ _
    (cellGeneratorLeg c x.1 x.2 ≫
      P.eraseAlgebra.map (c.F.map (homOfLE (Order.succ_le_of_lt x.1.property))))).f
      (cellDegree c x.1 x.2) _ = _
  rw [Adjunction.homEquiv_naturality_right]
  change (c.F.map (homOfLE (Order.succ_le_of_lt x.1.property))).hom.f (cellDegree c x.1 x.2)
    ((P.erase.freeAlgebraAdjunction.homEquiv _ _ (cellGeneratorLeg c x.1 x.2)).f
      (cellDegree c x.1 x.2) _) = _
  rw [cellGeneratorLeg]
  erw [eraseAttachment_generator_value]

end Operad

namespace BarrattEccles
attribute [local implicit_reducible] operad Operad.cellStageGeneratorSpheres
variable {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : (operad A).Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => (operad A).freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The actual free-presentation generator is the image of the actual attached generator. -/
lemma cellStageGeneratorValue_eq_attached (hX : IsInitial X) (j : J)
    (x : CellsBefore (Operad.CellsAt c) j)
    (z : sphereDegreeIndex.{u} (Operad.cellDegree c x.1 x.2) (Operad.cellDegree c x.1 x.2)) :
    cellStageGeneratorValue c hX j (Operad.cellDegree c x.1 x.2) ⟨x, z⟩ =
      (c.F.map (homOfLE (Order.succ_le_of_lt x.1.property))).hom.f
        (Operad.cellDegree c x.1 x.2)
        (Operad.attachedGenerator (c.attachCells x.1 x.2.1.down) x.2.2) := by
  let d := Operad.cellDegree c x.1 x.2
  have he := congrArg (fun g => g.f d
    ((singleObjXSelf (.up ℤ) d (𝟙_ (ModuleCat A))).inv (1 : A)))
      (Operad.cellStageGeneratorLeg_homEquiv c hX j x)
  rw [Operad.cellStageGeneratorLeg_value] at he
  rw [cellStageGeneratorValue]
  erw [sphereCoproductDegreeBasis_apply, sphereDegreeBasis_self_apply]
  exact he.symm

end BarrattEccles
end SerrePositivity.EInfinity

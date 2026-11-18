module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CellStageFreeNaturality
public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseFreeGenerators

/-!
# セル段の自由表示と指定生成元

## 概要
Berger–Moerdijk 命題 4.1 のセル段の自由表示は、付加する各球の指定射を保つ。

## 方針
球の余積の指定包含と、自由代数の比較の単位を照合する。

## 規約
自由表示の同型は微分を消した代数の間で使う。

## 使われ方
自由表示で定義した生成元の像を実際の付加生成元へ結びつける。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad
open CategoryTheory Limits HomologicalComplex HomotopicalAlgebra DifferentialGraded
attribute [local implicit_reducible] cellSphere cellStageGeneratorSpheres
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : P.Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => P.freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The inverse erasure/coproduct comparison preserves the specified inclusions. -/
@[reassoc]
lemma cellStageErasedGeneratorsIso_inv_ι (j : J) (x : CellsBefore (CellsAt c) j) :
    Sigma.ι (fun y : CellsBefore (CellsAt c) j => cellSphere c y.1 y.2) x ≫
      (cellStageErasedGeneratorsIso c j).inv =
      (eraseDifferential A).map (Sigma.ι (cellStageGeneratorSpheres c j) x) := by
  have h := congrArg (fun z => z ≫ (cellStageErasedGeneratorsIso c j).inv)
    (cellStageErasedGeneratorsIso_ι c j x)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id] at h
  exact h.symm

/-- The original free-stage comparison preserves each attached generating sphere. -/
@[reassoc]
lemma cellStageErasedFreeIso_generator (hX : IsInitial X) (j : J)
    (x : CellsBefore (CellsAt c) j) :
    cellStageLeg (c.F ⋙ P.eraseAlgebra) (CellsAt c)
      (fun k y => P.erase.freeAlgebraFunctor.obj (cellSphere c k y))
      (cellGeneratorLeg c) j x ≫ (cellStageErasedFreeIso c hX j).hom =
      P.erase.freeAlgebraFunctor.map
        ((eraseDifferential A).map (Sigma.ι (cellStageGeneratorSpheres c j) x)) ≫
        P.eraseFreeAlgebraIso.inv.app (∐ (cellStageGeneratorSpheres c j)) := by
  simp only [cellStageErasedFreeIso, Iso.trans_hom, Iso.symm_hom,
    CategoryTheory.Functor.mapIso_hom]
  rw [erasedCellStageFreeIso_generator_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    cellStageErasedGeneratorsIso_inv_ι]
  rfl

/-- The free-stage adjoint of each attached sphere is its original free generator image. -/
lemma cellStageGeneratorLeg_homEquiv (hX : IsInitial X) (j : J)
    (x : CellsBefore (CellsAt c) j) :
    P.erase.freeAlgebraAdjunction.homEquiv _ _
      (cellStageLeg (c.F ⋙ P.eraseAlgebra) (CellsAt c)
        (fun k y => P.erase.freeAlgebraFunctor.obj (cellSphere c k y))
        (cellGeneratorLeg c) j x) =
      (eraseDifferential A).map (Sigma.ι (cellStageGeneratorSpheres c j) x ≫
        P.schurUnit (∐ (cellStageGeneratorSpheres c j))) ≫
        (cellStageErasedFreeIso c hX j).inv.hom := by
  let E := eraseDifferential A
  let U := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase
  let q := cellStageErasedFreeIso c hX j
  let a := P.erase.freeAlgebraAdjunction
  let V := ∐ (cellStageGeneratorSpheres c j)
  have hi : a.homEquiv _ _ (P.eraseFreeAlgebraIso.inv.app V) =
      E.map (P.schurUnit V) := by
    change a.unit.app (E.obj V) ≫ U.map (P.eraseFreeAlgebraIso.inv.app V) = _
    rw [P.eraseFreeAlgebraIso_inv_unit, P.freeAlgebraAdjunction_unit_app]
  have he := congrArg (a.homEquiv _ _) (cellStageErasedFreeIso_generator c hX j x)
  rw [a.homEquiv_naturality_right, a.homEquiv_naturality_left] at he
  erw [hi, ← E.map_comp] at he
  apply (cancel_mono (U.mapIso q).hom).mp
  change _ ≫ U.map q.hom = (_ ≫ U.map q.inv) ≫ U.map q.hom
  rw [Category.assoc, ← U.map_comp q.inv q.hom, q.inv_hom_id,
    U.map_id, Category.comp_id]
  exact he

end SerrePositivity.EInfinity.Operad

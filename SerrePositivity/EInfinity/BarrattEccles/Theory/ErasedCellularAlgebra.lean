module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.EraseCellAttachment
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TransfiniteCoproductCells
public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.Logic.Equiv.Option

/-!
# セル代数の各段の次数付き自由表示

## 概要
Berger–Moerdijk 命題 4.1 の始対象からの相対セル複体を、次数付き自由代数で表示する。

## 方針
後続段の自由付加と極限段の連続性を合わせ、各段までの生成元の余積を使う。

## 規約
元の小対象分解のセルと次数を保持する。

## 使われ方
セル代数の台の K 平坦性。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory Limits HomotopicalAlgebra DifferentialGraded

attribute [local irreducible] Operad.eraseAlgebra Operad.eraseFreeAlgebraIso

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : P.Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => P.freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The cells adjoined at a given stage, empty at a maximal stage. -/
abbrev CellsAt (j : J) := Σ h : PLift (¬ IsMax j), (c.attachCells j h.down).ι

/-- The degree of a generator at a successor stage. -/
def cellDegree (j : J) (x : CellsAt c j) : ℤ :=
  (c.attachCells j x.1.down).π x.2

/-- The erased sphere of the generator of the cell. -/
def cellSphere (j : J) (x : CellsAt c j) : Complex A :=
  (eraseDifferential A).obj (complexSphere A (cellDegree c j x))

/-- The specified free generator map after erasing the attachment. -/
def cellGeneratorLeg (j : J) (x : CellsAt c j) :
    P.erase.freeAlgebraFunctor.obj (cellSphere c j x) ⟶
      (c.F ⋙ P.eraseAlgebra).obj (Order.succ j) :=
  P.erase.freeAlgebraFunctor.map (erasedDiskSphereSplitting A (cellDegree c j x)).s ≫
    (P.eraseAttachment (c.attachCells j x.1.down)).cell x.2

set_option maxHeartbeats 800000 in
-- セルの再添字と余錐の図式の比較を、同じ宣言内で照合する。
/-- The erased stage is a coproduct of the free algebras on its earlier cells. -/
def erasedCellStageCofanIsColimit (hX : IsInitial X) (j : J) :
    IsColimit (cellStageCofan (c.F ⋙ P.eraseAlgebra) (CellsAt c)
      (fun k x => P.erase.freeAlgebraFunctor.obj (cellSphere c k x)) (cellGeneratorLeg c) j) := by
  let E := P.eraseAlgebra
  letI : PreservesWellOrderContinuousOfShape J E :=
    ⟨fun _ _ => inferInstance⟩
  let d := c.toTransfiniteCompositionOfShape.map E
  letI : (c.F ⋙ E).IsWellOrderContinuous := d.isWellOrderContinuous
  have h₀ : IsInitial ((c.F ⋙ E).obj ⊥) :=
    (hX.isInitialObj E _).ofIso d.isoBot.symm
  apply cellStageCofanIsColimit _ _ _ _ h₀
  intro k hk
  let a := c.attachCells k hk
  let e : CellsAt c k ≃ a.ι :=
    { toFun := fun x => x.2
      invFun := fun i => ⟨PLift.up hk, i⟩
      left_inv := by rintro ⟨⟨h⟩, i⟩; rfl
      right_inv := fun _ => rfl }
  let V (i : Option (CellsAt c k)) : P.erase.Algebra :=
    i.elim ((c.F ⋙ E).obj k)
      (fun x => P.erase.freeAlgebraFunctor.obj (cellSphere c k x))
  let W (i : Option a.ι) : P.erase.Algebra :=
    i.elim (E.obj (c.F.obj k)) (fun x =>
      P.erase.freeAlgebraFunctor.obj ((eraseDifferential A).obj (complexSphere A (a.π x))))
  let s : Cofan W := attachComplementCofan (P.eraseAttachment a)
    (fun n => P.erase.freeAlgebraFunctor.map (erasedDiskSphereSplitting A n).s)
  let q := Discrete.equivalence (Equiv.optionCongr e)
  let α : Discrete.functor V ≅ q.functor ⋙ Discrete.functor W :=
    Discrete.natIso (fun ⟨i⟩ => by cases i <;> exact Iso.refl _)
  let b := (P.eraseAttachmentCofanIsColimit a).whiskerEquivalence q
  let b' := (IsColimit.precomposeHomEquiv α (s.whisker q.functor)).symm b
  apply IsColimit.ofIsoColimit b'
  refine Cocone.ext (Iso.refl _) ?_
  rintro ⟨(_ | ⟨h, i⟩)⟩
  · simp [s, α, q, E, Equiv.optionCongr, attachComplementCofan]
  · have he : h = PLift.up hk := Subsingleton.elim _ _
    subst h
    simp [s, α, q, Equiv.optionCongr, attachComplementCofan,
      cellGeneratorLeg, cellDegree, e]
    rfl


/-- The erased stage is free on the coproduct of the spheres of its earlier cells. -/
def erasedCellStageFreeIso (hX : IsInitial X) (j : J) :
    (c.F ⋙ P.eraseAlgebra).obj j ≅
      P.erase.freeAlgebraFunctor.obj (∐ (fun x : CellsBefore (CellsAt c) j =>
        cellSphere c x.1 x.2)) := by
  letI := P.erase.freeAlgebraAdjunction.isLeftAdjoint
  let V (x : CellsBefore (CellsAt c) j) := cellSphere c x.1 x.2
  let D := isColimitCofanMkObjOfIsColimit P.erase.freeAlgebraFunctor V
    (Sigma.ι V) (colimit.isColimit (Discrete.functor V))
  exact (erasedCellStageCofanIsColimit c hX j).coconePointUniqueUpToIso D

/-- The free-stage comparison sends each specified generator to its coproduct inclusion. -/
@[reassoc]
lemma erasedCellStageFreeIso_generator (hX : IsInitial X) (j : J)
    (x : CellsBefore (CellsAt c) j) :
    cellStageLeg (c.F ⋙ P.eraseAlgebra) (CellsAt c)
      (fun k y => P.erase.freeAlgebraFunctor.obj (cellSphere c k y)) (cellGeneratorLeg c) j x ≫
        (erasedCellStageFreeIso c hX j).hom =
      P.erase.freeAlgebraFunctor.map (Sigma.ι (fun y : CellsBefore (CellsAt c) j =>
        cellSphere c y.1 y.2) x) := by
  let _ := P.erase.freeAlgebraAdjunction.isLeftAdjoint
  let V (y : CellsBefore (CellsAt c) j) := cellSphere c y.1 y.2
  let D := isColimitCofanMkObjOfIsColimit P.erase.freeAlgebraFunctor V
    (Sigma.ι V) (colimit.isColimit (Discrete.functor V))
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (erasedCellStageCofanIsColimit c hX j) D (Discrete.mk x)

/-- The map of generator coproducts for inclusion of one stage in a later stage. -/
def cellSphereCoproductMap {j k : J} (h : j ≤ k) :
    (∐ (fun x : CellsBefore (CellsAt c) j => cellSphere c x.1 x.2)) ⟶
      ∐ (fun x : CellsBefore (CellsAt c) k => cellSphere c x.1 x.2) :=
  Sigma.desc (fun x => Sigma.ι
    (fun y : CellsBefore (CellsAt c) k => cellSphere c y.1 y.2)
    (cellsBeforeInclusion (CellsAt c) h x))

/-- The free-stage comparisons are natural for the actual stage maps. -/
lemma erasedCellStageFreeIso_naturality (hX : IsInitial X) {j k : J} (h : j ≤ k) :
    (c.F ⋙ P.eraseAlgebra).map (homOfLE h) ≫ (erasedCellStageFreeIso c hX k).hom =
      (erasedCellStageFreeIso c hX j).hom ≫ P.erase.freeAlgebraFunctor.map
        (cellSphereCoproductMap c h) := by
  apply Cofan.IsColimit.hom_ext (erasedCellStageCofanIsColimit c hX j)
  intro x
  change cellStageLeg _ _ _ _ j x ≫ _ = cellStageLeg _ _ _ _ j x ≫ _
  rw [cellStageLeg_comp_assoc, erasedCellStageFreeIso_generator,
    erasedCellStageFreeIso_generator_assoc, ← CategoryTheory.Functor.map_comp,
    cellSphereCoproductMap, Sigma.ι_comp_desc]

end SerrePositivity.EInfinity.Operad

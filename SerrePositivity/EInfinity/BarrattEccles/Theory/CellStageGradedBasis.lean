module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.ErasedCellularAlgebra
public import SerrePositivity.EInfinity.BarrattEccles.Theory.SphereCoproductBasis
public import SerrePositivity.EInfinity.BarrattEccles.Theory.SchurWordBasis
public import SerrePositivity.EInfinity.BarrattEccles.OperadStructure

/-!
# セル代数の台の次数付き基底

## 概要
Berger–Moerdijk 命題 4.1 の始対象からのセル代数の台を、実際の Schur 表示へ移す。

## 方針
次数付きの自由表示と自由代数の随伴の比較を合わせ、元の係数オペラッドの基底を使う。

## 規約
セルの識別子、付加された次数、各段の指定射を保持する。

## 使われ方
セル代数の微分を基底で展開し、先行セルへの整礎再帰で重みを付ける。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory Limits HomotopicalAlgebra DifferentialGraded

namespace Operad

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : P.Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => P.freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The original spheres of all cells adjoined before a given stage. -/
def cellStageGeneratorSpheres (j : J) (x : CellsBefore (CellsAt c) j) : Complex A :=
  complexSphere A (cellDegree c x.1 x.2)

/-- Erasing the generator coproduct agrees with the coproduct of the erased spheres. -/
def cellStageErasedGeneratorsIso (j : J) :
    (eraseDifferential A).obj (∐ (cellStageGeneratorSpheres c j)) ≅
      ∐ (fun x : CellsBefore (CellsAt c) j => cellSphere c x.1 x.2) := by
  let E := eraseDifferential A
  let V := cellStageGeneratorSpheres c j
  let h := isColimitCofanMkObjOfIsColimit E V (Sigma.ι V)
    (colimit.isColimit (Discrete.functor V))
  exact h.coconePointUniqueUpToIso (colimit.isColimit (Discrete.functor _))

/-- The erased stage is the erased free algebra on the original generator spheres. -/
def cellStageErasedFreeIso (hX : IsInitial X) (j : J) :
    P.eraseAlgebra.obj (c.F.obj j) ≅
      P.eraseAlgebra.obj (P.freeAlgebraFunctor.obj (∐ (cellStageGeneratorSpheres c j))) :=
  erasedCellStageFreeIso c hX j ≪≫
    P.erase.freeAlgebraFunctor.mapIso (cellStageErasedGeneratorsIso c j).symm ≪≫
      (P.eraseFreeAlgebraIso.app (∐ (cellStageGeneratorSpheres c j))).symm

/-- Each actual carrier degree is the degree of the original Schur free algebra. -/
def cellStageSchurDegreeIso (hX : IsInitial X) (j : J) (i : ℤ) :
    (c.F.obj j).carrier.X i ≅
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurFunctor A P.sequence).obj (∐ (cellStageGeneratorSpheres c j))).X i := by
  let e := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase).mapIso (cellStageErasedFreeIso c hX j)
  change ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase).obj (P.eraseAlgebra.obj (c.F.obj j))).X i ≅
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase).obj (P.eraseAlgebra.obj
      (P.freeAlgebraFunctor.obj (∐ (cellStageGeneratorSpheres c j))))).X i
  exact (HomologicalComplex.eval (ModuleCat A) (.up ℤ) i).mapIso
    (X := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase).obj (P.eraseAlgebra.obj (c.F.obj j)))
    (Y := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P.erase).obj (P.eraseAlgebra.obj
      (P.freeAlgebraFunctor.obj (∐ (cellStageGeneratorSpheres c j))))) e

end Operad

namespace BarrattEccles

variable {A : Type u} [CommRing A]
  {J : Type u} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {X Y : (operad A).Algebra} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u}
    (fun (_ : J) n => (operad A).freeAlgebraFunctor.map (complexSphereToDisk A n)) f)

/-- The actual cell carrier has the basis indexed by coefficient simplices and cell inputs. -/
def cellStageWordBasis (hX : IsInitial X) (j : J) (i : ℤ) :
    Module.Basis
      (SchurWordIndex
        (SphereCoproductIndex (fun x : CellsBefore (Operad.CellsAt c) j =>
          Operad.cellDegree c x.1 x.2)) i)
      A ((c.F.obj j).carrier.X i) :=
  (schurWordBasis (sphereCoproductDegreeBasis
    (fun x : CellsBefore (Operad.CellsAt c) j => Operad.cellDegree c x.1 x.2)) i).map
      (Operad.cellStageSchurDegreeIso c hX j i).symm.toLinearEquiv

end BarrattEccles

end SerrePositivity.EInfinity

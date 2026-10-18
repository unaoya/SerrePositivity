module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
概要：左完全関手と短複体のサイクルの比較。
方針：サイクルを核として扱い、有限極限の保存だけを使う。
規約：コホモロジーや余核の保存は要求しない。
使われ方：TT §3、Toën §3.2 の層のサイクルと切断のサイクルの接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v a b
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type a} [Category.{b} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (S : ShortComplex C)

/--
概要：左完全関手で写した短複体のサイクルは元のサイクルの像と同型。
方針：写した核の錐と選ばれたサイクルの核の普遍性を比較する。
規約：関手に右完全性を仮定しない。
使われ方：TT §3、Toën §3.2 の大域切断とサイクル。
-/
def leftExactCyclesIso : (S.map F).cycles ≅ F.obj S.cycles :=
  ((S.map F).isoCyclesOfIsLimit
    (isLimitForkMapOfIsLimit' F S.iCycles_g S.cyclesIsKernel)).symm

/--
概要：左完全関手のサイクル比較は元の包含写像と可換。
方針：核の比較同型の標準の射影公式を使う。
規約：同じ関手とサイクルの射を保持する。
使われ方：TT §3、Toën §3.2 の切断の境界等式。
-/
lemma leftExactCyclesIso_hom_iCycles :
    (leftExactCyclesIso F S).hom ≫ F.map S.iCycles = (S.map F).iCycles :=
  (S.map F).isoCyclesOfIsLimit_inv_ι
    (isLimitForkMapOfIsLimit' F S.iCycles_g S.cyclesIsKernel)

end SerrePositivity.KST.DerivedGeometry

module
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Types.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic

/-!
概要：三角形の円柱を構成する三つの三単体。
方針：空間座標に退化写像、時刻座標に三つの切り替え位置を使う。
規約：任意の単体集合と任意の円柱上の射を扱う。
使われ方：錐の三角形の比較円柱に四面の合成則を適用する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：三角形の円柱の三つの三単体の時刻座標。
方針：頂点 i の後で時刻が 0 から 1 に移る単調写像を使う。
規約：一次元の区間の向きを 0 から 1 とする。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
def trianglePrismTime (i : Fin 3) : (Δ[1] : SSet.{u}) _⦋3⦌ :=
  stdSimplex.objEquiv.symm (SimplexCategory.mkHom {
    toFun := fun j : Fin 4 ↦ if j.val ≤ i.val then (0 : Fin 2) else 1
    monotone' := by
      intro a b hab
      dsimp
      split_ifs with ha hb hb
      · exact le_refl _
      · exact Fin.zero_le _
      · have hab' := Fin.le_iff_val_le_val.mp hab
        omega
      · exact le_refl _ })
/-- 概要：三角形のホモトピーを分割する三つの三単体。
方針：一つの頂点を繰り返し、対応する時刻列と組にして写す。
規約：区間の向きを 0 から 1 とする。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
def triangleHomotopyTetrahedron {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y)
    (s : X _⦋2⦌) (i : Fin 3) : Y _⦋3⦌ :=
  H.app (Opposite.op ⦋3⦌) (X.σ i s, trianglePrismTime i)
/-- 概要：最初の三単体の上面では時刻が 1 に定値。
方針：三頂点を場合分けして計算する。
規約：区間の向きを 0 から 1 とする。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
lemma trianglePrismTime_first :
    (Δ[1] : SSet.{u}).δ 0 (trianglePrismTime 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) 2 := by
  apply stdSimplex.ext
  intro j
  fin_cases j <;> rfl
/-- 概要：最後の三単体の下面では時刻が 0 に定値。
方針：三頂点を場合分けして計算する。
規約：区間の向きを 0 から 1 とする。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
lemma trianglePrismTime_last :
    (Δ[1] : SSet.{u}).δ 3 (trianglePrismTime 2) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) 2 := by
  apply stdSimplex.ext
  intro j
  fin_cases j <;> rfl
/-- 概要：最初と中央の三単体の共有面の時刻が一致。
方針：三頂点を場合分けして計算する。
規約：区間の向きを 0 から 1 とする。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
lemma trianglePrismTime_glue_first :
    (Δ[1] : SSet.{u}).δ 1 (trianglePrismTime 0) =
      (Δ[1] : SSet.{u}).δ 1 (trianglePrismTime 1) := by
  apply stdSimplex.ext
  intro j
  fin_cases j <;> rfl
/-- 概要：中央と最後の三単体の共有面の時刻が一致。
方針：三頂点を場合分けして計算する。
規約：区間の向きを 0 から 1 とする。
使われ方：全錐の比較円柱への四面の合成則の適用。 -/
lemma trianglePrismTime_glue_last :
    (Δ[1] : SSet.{u}).δ 2 (trianglePrismTime 1) =
      (Δ[1] : SSet.{u}).δ 2 (trianglePrismTime 2) := by
  apply stdSimplex.ext
  intro j
  fin_cases j <;> rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

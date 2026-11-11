module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SelfPullbackInverseComponents
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyComponents

/-!
概要：自己 pullback の交換と零次数への連結写像の逆元の式。
方針：連結射の代表を逆元の辺の構成へ渡し、代表によらない式に戻す。
規約：全空間の収縮可能性は不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。三角形の交換を基本群の逆元として計算する。

対応節は Kerodon 3.2（Tag 00V2）。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups
open _root_.SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：基本群の連結射を自己 pullback の成分へ送る。
方針：fiber の成分へ向かう連結射の後に第一因子への包含を合成する。
規約：第二因子は指定した全空間の基点。
使われ方：Goerss–Jardine I §7。二因子の交換と逆元の比較の写像。 -/
def selfPullbackConnecting {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (p.app _ e) → π₀ (pullback p p) :=
  fun a => mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyZero.equivPiZero (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e 0 a))

/-- 概要：自己 pullback への連結射を任意の持ち上げの代表で計算する。
方針：連結射の代表の式と零次数の π₀ との比較を使う。
規約：代表を選ぶ方法は任意。
使われ方：Kerodon §3.2.5（Tag 00WD）。逆元の三角形の成分の式との接続。 -/
theorem selfPullbackConnecting_eq {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌)
    {s : B.PtSimplex 1 (p.app _ e)} (L : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.BoundaryLift p e s) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent (L.boundary.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackFiberInclusion p e) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_eq p e L]
  rfl

/-- 概要：自己 pullback の二因子の交換は連結射の像上で基本群の逆元に対応する。
方針：各基本群の代表について逆元の三角形を選び、pullback 内の辺で比較する。
規約：全空間の収縮可能性を仮定しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。二重 loop の交換の符号を決める一般式。 -/
theorem selfPullbackConnecting_swap {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (p.app _ e)) :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackSwap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p e a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p e a⁻¹ := by
  induction a using Quotient.inductionOn with | h s => ?_
  change mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackSwap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p e (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)⁻¹
  let Ls := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.chooseBoundaryLift p e s
  obtain ⟨t, Lt, ht, hπ⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullback_swap_inverse_representative p e s Ls
  rw [← ht, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_eq p e Ls, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_eq p e Lt,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.zeroMapComponent_comp]
  exact hπ.symm

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackConnecting := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackConnecting_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackConnecting_swap := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_swap

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackConnecting._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting._proof_1

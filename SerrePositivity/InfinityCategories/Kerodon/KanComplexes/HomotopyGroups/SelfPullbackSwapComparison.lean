module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SelfPullbackNaturality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.SelfPullbackComponents

/-!
概要：底の基本群で逆元として作用する射と自己 pullback の交換を比較する。
方針：連結写像の自然性と全射性で全ての成分へ逆元の式を移す。
規約：全空間の指定基点を保つ自己射を使う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.6（Tag 00WL）。二重 loop の交換と loop の逆元の比較。

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

/-- 概要：等しい参照頂点への移送は自己 pullback の連結射の値を保つ。
方針：頂点の等式で帰納する。
規約：底の誘導写像の基点の等式も同時に移送する。
使われ方：Kerodon §3.2.5（Tag 00WD）。自然性の標的基点を指定基点へ戻す。 -/
theorem selfPullbackConnecting_map_point_eq {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (x y : E _⦋0⦌) (h : x = y) (b : B _⦋0⦌) (g : B ⟶ B)
    (hg : g.app _ b = p.app _ x) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p x (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g hg a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p y
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g (hg.trans (congrArg (p.app _) h)) a) := by
  subst y
  rfl

/-- 概要：基点を保つ可換自己四角形での自己 pullback の連結射の自然性。
方針：一般の自然性の標的基点を指定基点へ戻す。
規約：底の基点の等式は可換式と全空間の基点保存から得る。
使われ方：Goerss–Jardine I §7。基本群の逆元として作用する射への適用。 -/
theorem selfPullbackConnecting_natural_fixed {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    (f : E ⟶ E) (g : B ⟶ B) (comm : p ≫ g = f ≫ p)
    (e : E _⦋0⦌) (hf : f.app _ e = e) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (p.app _ e)) :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap p p f g comm) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p e a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting p e
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p f g comm e).trans (congrArg (p.app _) hf)) a) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_natural p p f g comm e a
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_map_point_eq p (f.app _ e) e hf
    (p.app _ e) g (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p f g comm e) a)

/-- 概要：底の基本群に逆元として作用する射は、連結な自己 pullback の成分で二因子の交換と一致。
方針：全成分を連結射で表し、その自然性と交換の逆元の式を使う。
規約：全空間の π₀ が一元で、全空間の自己射は指定基点を保つ。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.6（Tag 00WL）。二重 loop の交換の符号の一般的な判定。 -/
theorem selfPullbackMap_eq_swap_on_components {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (p : E ⟶ B) [Fibration p]
    [Subsingleton (π₀ E)] (f : E ⟶ E) (g : B ⟶ B) (comm : p ≫ g = f ≫ p)
    (e : E _⦋0⦌) (hf : f.app _ e = e)
    (hg : ∀ a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (p.app _ e),
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationSquare.base_eq p p f g comm e).trans (congrArg (p.app _) hf)) a = a⁻¹) :
    mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap p p f g comm) = mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackSwap p) := by
  funext a
  obtain ⟨b, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_surjective p e a
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_natural_fixed p f g comm e hf, hg,
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_swap]

end

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackConnecting_map_point_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_map_point_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackConnecting_natural_fixed := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackConnecting_natural_fixed

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.selfPullbackMap_eq_swap_on_components := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.selfPullbackMap_eq_swap_on_components

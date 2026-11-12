module

public import SerrePositivity.KST.Spectra.ZeroConnectingInjectivity
public import SerrePositivity.KST.Spectra.LoopHomotopyGroups

/-!
概要：loop の零次数のホモトピー類と標的の基本群の同値。
方針：三角形の全境界充填による連結写像の単射性と長完全列による全射性を使う。
規約：零次数の集合に予め群構造を仮定しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）、BF 1978 §2。Ω スペクトルの零次数。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

/-- 概要：全空間の零次数が一元で全境界を充填できる場合の零次数への連結同値。
方針：全三角形の充填による単射性と完全列による全射性を組み合わせる。
規約：fiber の零次数は集合として扱う。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）。loop の零次数の比較。 -/
def connectingZeroEquiv {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌)
    [Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy E 0 e)]
    (hE : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup B 0 (p.app _ e) ≃ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber p (p.app _ e)) 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint p e) :=
  Equiv.ofBijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting p e 0)
    ⟨connecting_zero_injective p e hE, fun a ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_connecting_fiber_all p e 0 a).1 (Subsingleton.elim _ _)⟩

/-- 概要：loop の連結成分は標的の基本群の元と同値。
方針：loop の fiber 表示と path fibration の零次数の連結同値を合成する。
規約：標的の基点への移送を明示する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.5（Tag 00WD）、BF 1978 §2。 -/
def loopZeroHomotopyEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right 0 Y.basepoint :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso 0 (loopBasedPathFiberIso Y) (loopBasedPathFiberIso_basepoint Y)).trans
    ((connectingZeroEquiv (pathEndpoint Y).right (basedPathSpace Y).basepoint
      (basedPathSpace_terminal_rlp Y)).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl Y.right) (pathEndpoint_basepoint Y)).toEquiv)

/-- 概要：全自然数次数で loop のホモトピー類は標的の一つ上の次数と同値。
方針：零次数の辺の充填と正次数の連結群同型をまとめる。
規約：ここでは集合の同値を述べる。正次数では構成済みの群同型がある。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。全次数の Ω 条件。 -/
def loopHomotopyEquiv (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right n (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy Y.right (n + 1) Y.basepoint :=
  match n with
  | 0 => loopZeroHomotopyEquiv Y
  | n + 1 => (loopPositiveHomotopyEquiv Y n).toEquiv

/-- 概要：零次数の連結同値の逆は fiber の基点を基本群の単位へ戻す。
方針：連結写像の単位保存と同値の単射性を使う。
規約：終対象への射の RLP と零次数の一元性を明示する。
使われ方：Goerss–Jardine I §7。零次数の群の単位の照合。 -/
@[simp]
theorem connectingZeroEquiv_symm_point {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    [KanComplex E] [KanComplex B] (e : E _⦋0⦌)
    [Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy E 0 e)]
    (hE : (MorphismProperty.monomorphisms SSet.{u}).rlp (terminal.from E)) :
    (connectingZeroEquiv p e hE).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point 0) = 1 := by
  apply (connectingZeroEquiv p e hE).injective
  rw [Equiv.apply_symm_apply]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connecting_one p e 0).symm

/-- 概要：loop の零次数の同値は定数 loop の類を基本群の単位へ送る。
方針：fiber 同型の基点保存と連結同値の単位の式を合成する。
規約：群構造の移送の単位が元の基点と一致することを検査する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。Ω スペクトルの零次数の群。 -/
@[simp]
theorem loopZeroHomotopyEquiv_point (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] :
    loopZeroHomotopyEquiv Y (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point 0) = 1 := by
  simp only [loopZeroHomotopyEquiv, Equiv.trans_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.equivOfIso_point,
    MulEquiv.toEquiv_eq_coe]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl Y.right) (pathEndpoint_basepoint Y))
    ((connectingZeroEquiv (pathEndpoint Y).right (basedPathSpace Y).basepoint
      (basedPathSpace_terminal_rlp Y)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.point 0)) = 1
  rw [connectingZeroEquiv_symm_point]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso 0 (Iso.refl Y.right) (pathEndpoint_basepoint Y)).map_one

end

end SerrePositivity.KST.Spectra

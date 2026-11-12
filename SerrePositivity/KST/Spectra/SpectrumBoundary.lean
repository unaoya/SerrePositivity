module

public import SerrePositivity.KST.Spectra.SpectrumFiberStage

/-!
概要：整数次数のスペクトルの fiber 列の連結準同型。
方針：十分高い正次数の一段で連結準同型を計算し、自然な段表示の同型で移す。
規約：δ_j は π_(j+1)(Y) から π_j(fiber) への準同型。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。全整数次数の長完全列。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：整数次数の連結射を計算する段。
方針：|j|+2 を取り、fiber の計算次数も正にする。
規約：j は連結射の標的の整数次数。
使われ方：BF 1978 §2。全ての整数で群の連結準同型を使う。 -/
def boundaryStage (j : ℤ) : ℕ := j.natAbs + 2

/-- 概要：指定段の連結準同型の自然数添字。
方針：fiber の実際の次数から一を引く。
規約：fiber の次数はこの添字に一を足したもの。
使われ方：Goerss–Jardine I §7、BF 1978 §2。段の連結準同型への接続。 -/
def boundaryIndex (j : ℤ) : ℕ := degree j (boundaryStage j) - 1

/-- 概要：連結射の計算段は fiber の整数次数に許される。
方針：整数の符号で場合分けして算術を使う。
規約：j は fiber の次数。
使われ方：BF 1978 §2。fiber の任意段表示。 -/
theorem boundaryStage_admissible (j : ℤ) : -j ≤ (boundaryStage j : ℤ) := by
  have h := canonicalLevel_admissible j
  unfold boundaryStage canonicalLevel at *
  omega

/-- 概要：同じ計算段は底の一つ上の整数次数にも許される。
方針：fiber の次数の非負性から従う。
規約：底の次数は j+1。
使われ方：BF 1978 §2。底の任意段表示。 -/
theorem boundaryStage_succ_admissible (j : ℤ) : -(j + 1) ≤ (boundaryStage j : ℤ) := by
  have h := boundaryStage_admissible j
  omega

/-- 概要：計算段での fiber の次数は連結添字に一を足したもの。
方針：符号ごとの計算で自然数への変換と減算を整理する。
規約：必ず正次数。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber の群の添字。 -/
theorem boundaryStage_degree (j : ℤ) : degree j (boundaryStage j) = boundaryIndex j + 1 := by
  cases j <;> simp [boundaryStage, boundaryIndex, degree] <;> omega

/-- 概要：同じ計算段での底の次数は連結添字に二を足したもの。
方針：整数の符号と自然数変換を計算する。
規約：底は二以上の次数で計算する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。群の連結準同型の始域。 -/
theorem boundaryStage_succ_degree (j : ℤ) :
    degree (j + 1) (boundaryStage j) = boundaryIndex j + 2 := by
  cases j <;> simp [boundaryStage, boundaryIndex, degree] <;> omega

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) [hp : ∀ k, Fibration (p.app k).right]

/-- 概要：連結射の底の整数次数群を、計算段の像の基点で表示する。
方針：正次数の段の表示に恒等射による基点移送を合成する。
規約：実際の底の次数は boundaryIndex j + 2。
使われ方：Goerss–Jardine I §7、BF 1978 §2。整数次数の連結射の始域。 -/
def boundaryBaseEquiv (j : ℤ) : homotopyGroup Y (j + 1) ≃*
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (Y.level (boundaryStage j)).space.right (boundaryIndex j + 1)
      ((p.app (boundaryStage j)).right.app _ (X.level (boundaryStage j)).space.basepoint) :=
  (positiveStageEquiv Y (j + 1) (boundaryStage j) (boundaryIndex j + 1)
    (boundaryStage_succ_admissible j) (boundaryStage_succ_degree j)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (boundaryIndex j + 1)
        (Iso.refl (Y.level (boundaryStage j)).space.right)
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p.app (boundaryStage j)))).symm

/-- 概要：連結射の fiber の整数次数群を計算段の実際の fiber で表示する。
方針：段の自然な表示と置換の比較射の群同型を使う。
規約：実際の fiber の次数は boundaryIndex j + 1。
使われ方：Goerss–Jardine I §7、BF 1978 §2。整数次数の連結射の標的。 -/
def boundaryFiberEquiv (j : ℤ) : homotopyGroup (fiber p hp) j ≃*
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanFiber (p.app (boundaryStage j)).right
      ((p.app (boundaryStage j)).right.app _ (X.level (boundaryStage j)).space.basepoint))
      (boundaryIndex j) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberPoint (p.app (boundaryStage j)).right
        (X.level (boundaryStage j)).space.basepoint) :=
  fiberPositiveStageEquiv p j (boundaryStage j) (boundaryIndex j)
    (boundaryStage_admissible j) (boundaryStage_degree j)

/-- 概要：整数次数の fiber 列の連結準同型。
方針：段の連結準同型を二つの段表示の群同型で移す。
規約：π_(j+1)(Y) → π_j(fiber p)、全ての整数 j で定義する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。スペクトルの長完全列。 -/
def stableConnectingHom (j : ℤ) : homotopyGroup Y (j + 1) →* homotopyGroup (fiber p hp) j :=
  (boundaryFiberEquiv p j).symm.toMonoidHom.comp
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom (p.app (boundaryStage j)).right
      (X.level (boundaryStage j)).space.basepoint (boundaryIndex j)).comp
        (boundaryBaseEquiv p j).toMonoidHom)

/-- 概要：整数次数の連結準同型は指定段の連結準同型で計算できる。
方針：群同型の順逆の合成を打ち消す。
規約：始域と標的の段表示を両方明示する。
使われ方：Goerss–Jardine I §7、BF 1978 §2。完全性の段からの移送。 -/
theorem stableConnectingHom_compute (j : ℤ) (a : homotopyGroup Y (j + 1)) :
    boundaryFiberEquiv p j (stableConnectingHom p j a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom (p.app (boundaryStage j)).right
        (X.level (boundaryStage j)).space.basepoint (boundaryIndex j) (boundaryBaseEquiv p j a) :=
  (boundaryFiberEquiv p j).apply_symm_apply _

omit hp in
/-- 概要：底の段表示は元の射の整数次数の写像を段の fibration の写像へ送る。
方針：正次数の段表示の自然性と基点移送の計算を使う。
規約：整数次数は j+1。
使われ方：Goerss–Jardine I §7、BF 1978 §2。底の位置の完全性。 -/
theorem boundaryBaseEquiv_projection (j : ℤ) (a : homotopyGroup X (j + 1)) :
    boundaryBaseEquiv p j (homotopyMap p (j + 1) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (p.app (boundaryStage j)).right rfl
        (positiveStageEquiv X (j + 1) (boundaryStage j) (boundaryIndex j + 1)
          (boundaryStage_succ_admissible j) (boundaryStage_succ_degree j) a) :=
  positiveStageEquiv_projection p _ _ _ _ _ a

/-- 概要：fiber の段表示は整数次数の包含を実際の段の fiber 包含へ送る。
方針：既証の fiber の正次数の段の比較を使う。
規約：整数次数は j。
使われ方：Goerss–Jardine I §7、BF 1978 §2。fiber の位置の完全性。 -/
theorem boundaryFiberEquiv_inclusion (j : ℤ) (a : homotopyGroup (fiber p hp) j) :
    positiveStageEquiv X j (boundaryStage j) (boundaryIndex j)
      (boundaryStage_admissible j) (boundaryStage_degree j)
        (homotopyMap (fiberInclusion p hp) j a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (p.app (boundaryStage j)).right
        ((p.app (boundaryStage j)).right.app _ (X.level (boundaryStage j)).space.basepoint))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point (p.app (boundaryStage j)).right (X.level (boundaryStage j)).space.basepoint)
          (boundaryFiberEquiv p j a) :=
  fiberPositiveStageEquiv_inclusion p _ _ _ _ _ a

end

end SerrePositivity.KST.Spectra.OmegaSpectrum

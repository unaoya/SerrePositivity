module

public import SerrePositivity.KST.Spectra.SpectrumBoundary
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.GroupExactTransfer

/-!
概要：段ごとの Kan fibration のスペクトルの fiber 列の整数次数長完全列。
方針：正次数の段の長完全列を三つの群同型で移す。
規約：δ_j : π_(j+1)(Y) → π_j(fiber)、全ての整数 j で群の核と像が一致する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。KST の π_* 同型による完全性。
-/

@[expose] public section

universe u

open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.OmegaSpectrum

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : OmegaSpectrum.{u}} (p : X ⟶ Y) [hp : ∀ k, Fibration (p.app k).right]

/-- 概要：整数次数の fiber の包含の核は連結準同型の像。
方針：計算段の fiber の位置の完全性を自然な群同型で移す。
規約：全ての整数 j で有効。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。長完全列の fiber の位置。 -/
theorem stable_exact_connecting_fiber (j : ℤ) (a : homotopyGroup (fiber p hp) j) :
    homotopyMap (fiberInclusion p hp) j a = 1 ↔
      ∃ b : homotopyGroup Y (j + 1), stableConnectingHom p j b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (stableConnectingHom p j) (homotopyMap (fiberInclusion p hp) j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom (p.app (boundaryStage j)).right
      (X.level (boundaryStage j)).space.basepoint (boundaryIndex j))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (p.app (boundaryStage j)).right
      ((p.app (boundaryStage j)).right.app _ (X.level (boundaryStage j)).space.basepoint))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point (p.app (boundaryStage j)).right (X.level (boundaryStage j)).space.basepoint))
    (boundaryBaseEquiv p j) (boundaryFiberEquiv p j)
    (positiveStageEquiv X j (boundaryStage j) (boundaryIndex j)
      (boundaryStage_admissible j) (boundaryStage_degree j))
    (stableConnectingHom_compute p j) (boundaryFiberEquiv_inclusion p j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_connecting_fiber (p.app (boundaryStage j)).right
      (X.level (boundaryStage j)).space.basepoint (boundaryIndex j)) a

/-- 概要：整数次数の連結準同型の核は全空間から底への準同型の像。
方針：計算段の底の位置の完全性を群同型で移す。
規約：全ての整数 j に対して π_(j+1)(Y) での完全性。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。長完全列の底の位置。 -/
theorem stable_exact_total_base (j : ℤ) (a : homotopyGroup Y (j + 1)) :
    stableConnectingHom p j a = 1 ↔
      ∃ b : homotopyGroup X (j + 1), homotopyMap p (j + 1) b = a :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (homotopyMap p (j + 1)) (stableConnectingHom p j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := boundaryIndex j + 1) (p.app (boundaryStage j)).right rfl)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.connectingHom (p.app (boundaryStage j)).right
      (X.level (boundaryStage j)).space.basepoint (boundaryIndex j))
    (positiveStageEquiv X (j + 1) (boundaryStage j) (boundaryIndex j + 1)
      (boundaryStage_succ_admissible j) (boundaryStage_succ_degree j))
    (boundaryBaseEquiv p j) (boundaryFiberEquiv p j)
    (boundaryBaseEquiv_projection p j) (stableConnectingHom_compute p j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_total_base (p.app (boundaryStage j)).right
      (X.level (boundaryStage j)).space.basepoint (boundaryIndex j)) a

/-- 概要：整数次数の全空間から底への準同型の核は fiber 包含の像。
方針：計算段の全空間の位置の完全性を自然な段表示と基点移送で移す。
規約：全ての整数 j で有効。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。長完全列の全空間の位置。 -/
theorem stable_exact_fiber_total (j : ℤ) (a : homotopyGroup X j) :
    homotopyMap p j a = 1 ↔
      ∃ b : homotopyGroup (fiber p hp) j, homotopyMap (fiberInclusion p hp) j b = a := by
  let eY := (positiveStageEquiv Y j (boundaryStage j) (boundaryIndex j)
    (boundaryStage_admissible j) (boundaryStage_degree j)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfIso (boundaryIndex j)
        (Iso.refl (Y.level (boundaryStage j)).space.right)
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p.app (boundaryStage j)))).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.group_exact_of_equivalences (homotopyMap (fiberInclusion p hp) j) (homotopyMap p j)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (p.app (boundaryStage j)).right
      ((p.app (boundaryStage j)).right.app _ (X.level (boundaryStage j)).space.basepoint))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι_point (p.app (boundaryStage j)).right (X.level (boundaryStage j)).space.basepoint))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := boundaryIndex j) (p.app (boundaryStage j)).right rfl)
    (boundaryFiberEquiv p j)
    (positiveStageEquiv X j (boundaryStage j) (boundaryIndex j)
      (boundaryStage_admissible j) (boundaryStage_degree j)) eY
    (boundaryFiberEquiv_inclusion p j) (positiveStageEquiv_projection p j _ _ _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.exact_fiber_total (p.app (boundaryStage j)).right
      (X.level (boundaryStage j)).space.basepoint (boundaryIndex j)) a

/-- 概要：スペクトルの fiber 列のホモトピー群の長完全列は全整数次数で完全。
方針：fiber・全空間・底の三つの位置の核と像の一致を束ねる。
規約：各段が Kan fibration の射を入力とし、fiber は単射置換済みの BF 対象。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。KST の全次数の完全列。 -/
theorem stableFiberLongExact :
    (∀ (j : ℤ) (a : homotopyGroup (fiber p hp) j),
      homotopyMap (fiberInclusion p hp) j a = 1 ↔
        ∃ b : homotopyGroup Y (j + 1), stableConnectingHom p j b = a) ∧
    (∀ (j : ℤ) (a : homotopyGroup X j), homotopyMap p j a = 1 ↔
      ∃ b : homotopyGroup (fiber p hp) j, homotopyMap (fiberInclusion p hp) j b = a) ∧
    (∀ (j : ℤ) (a : homotopyGroup Y (j + 1)), stableConnectingHom p j a = 1 ↔
      ∃ b : homotopyGroup X (j + 1), homotopyMap p (j + 1) b = a) :=
  ⟨stable_exact_connecting_fiber p, stable_exact_fiber_total p, stable_exact_total_base p⟩

/-- 概要：連結準同型の後の fiber 包含との合成は全整数次数で自明。
方針：fiber の位置の完全性に連結射の像であることを使う。
規約：乗法記法なので自明な値は単位。
使われ方：BF 1978 §2、HA §1.4.2。長完全列の零合成。 -/
@[simp]
theorem stableConnectingHom_inclusion (j : ℤ) (a : homotopyGroup Y (j + 1)) :
    homotopyMap (fiberInclusion p hp) j (stableConnectingHom p j a) = 1 :=
  (stable_exact_connecting_fiber p j _).2 ⟨a, rfl⟩

/-- 概要：元の射の後の連結準同型との合成は全整数次数で自明。
方針：底の位置の完全性に全空間の像であることを使う。
規約：乗法記法なので自明な値は単位。
使われ方：BF 1978 §2、HA §1.4.2。長完全列の零合成。 -/
@[simp]
theorem stableConnectingHom_projection (j : ℤ) (a : homotopyGroup X (j + 1)) :
    stableConnectingHom p j (homotopyMap p (j + 1) a) = 1 :=
  (stable_exact_total_base p j _).2 ⟨a, rfl⟩

/-- 概要：fiber 包含と元の射の誘導準同型の合成は全整数次数で自明。
方針：全空間の位置の完全性を使う。
規約：fiber は単射置換を挟んだ対象。
使われ方：BF 1978 §2、HA §1.4.2。長完全列の零合成。 -/
@[simp]
theorem homotopyMap_fiberInclusion (j : ℤ) (a : homotopyGroup (fiber p hp) j) :
    homotopyMap p j (homotopyMap (fiberInclusion p hp) j a) = 1 :=
  (stable_exact_fiber_total p j _).2 ⟨a, rfl⟩

end

end SerrePositivity.KST.Spectra.OmegaSpectrum

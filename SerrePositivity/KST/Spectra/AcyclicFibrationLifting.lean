module
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.F1PointedAcyclicFibrationLifting

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.FibrationIntervalLifting
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence

/-!
概要：π_* 同型である非空な Kan fibration の全単射 RLP。
方針：底の単体を頂点へ収縮し、fiber の充填を相対区間充填で元の正方形へ戻す。
規約：源の非空性を参照頂点で指定する。HT-KQ は使わない。
使われ方：Goerss–Jardine I §§7–8、Kerodon §3.2.6（Tag 00WL）、BF 1978 §2。Whitehead の充填による証明。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：非空な Kan 複体間の Kan fibration の全基点 π_* 同型性と全単射 RLP は同値。
方針：相対 Whitehead の充填と、RLP からの実際の収縮による既存の逆向きを合わせる。
規約：弱同値のクラスを追加定義せず、二つの明示的な条件を比較する。
使われ方：Goerss–Jardine I §§7–8、BF 1978 §2。写像空間の π_* 比較と逆射の実現。 -/
theorem fibration_piIsomorphism_iff_rlp {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (p : E ⟶ B) [Fibration p] (e₀ : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism p ↔ (MorphismProperty.monomorphisms SSet.{u}).rlp p :=
  ⟨fun hp ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_rlp_of_piIsomorphism p hp e₀, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight p⟩

end

end SerrePositivity.KST.Spectra

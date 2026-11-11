module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.RightHornContractions
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.LastHornPullback

/-!
概要：left fibration に沿う全ての右ホーンの引き戻しは right anodyne。
方針：右ホーンの二段収縮と標準単体の収縮で共通の終点 fiber から比較する。
規約：ホーン番号は零以外。内側ホーンを含み、全空間の quasicategory 性は不要。
使われ方：cofinality の引き戻しの安定性を弱飽和閉包へ移す生成元。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：left fibration に沿う右ホーンの引き戻しは right cofinal。
方針：二段の固定した終点収縮を持ち上げ、共通 fiber からの消去則を使う。
規約：k ≠ 0。外側と内側を統一する。
使われ方：右ホーンの引き戻しの right anodyne 判定。 -/
lemma leftFibration_rightHorn_pullback_isRightCofinal {E : SSet.{u}}
    (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0)
    (p : E ⟶ (Δ[n + 1] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal (pullback.fst p (horn (n + 1) k).ι) := by
  let f := (horn.{u} (n + 1) k).ι
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p f) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_pullback_fst_of_vertexFibers p f (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalRightHornVertex n k hk)
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isRightCofinal_of_rightAnodyne
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_terminalFiber_rightAnodyne_of_two_fixed_contractions _ _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalRightHornRaise n k) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalRightHornFinish n k hk)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalRightHornRaise_zero n k) rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalRightHornFinish_zero n k hk)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalRightHornFinish_one n k hk) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalRightHornRaise_const n k hk)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalRightHornFinish_const n k hk)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.leftFibration_terminalFiber_isRightCofinal p

/-- 概要：left fibration に沿う全ての右ホーンの引き戻しは right anodyne。
方針：証明した right cofinality と引き戻しの単射性による判定。
規約：内側ホーンも含む生成元ごとの定理。
使われ方：一般の right anodyne な射に拡張する弱飽和閉包の計算。 -/
lemma leftFibration_rightHorn_pullback_rightAnodyne {E : SSet.{u}}
    (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0)
    (p : E ⟶ (Δ[n + 1] : SSet.{u})) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (pullback.fst p (horn (n + 1) k).ι) :=
  (leftFibration_rightHorn_pullback_isRightCofinal n k hk p).rightAnodyneExtensions

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

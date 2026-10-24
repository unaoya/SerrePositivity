module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.RightHornContractions
public import SerrePositivity.InfinityCategories.F1B.Fibrations.LastHornPullback

/-!
概要：left fibration に沿う全ての右ホーンの引き戻しは right anodyne。
方針：右ホーンの二段収縮と標準単体の収縮で共通の終点 fiber から比較する。
規約：ホーン番号は零以外。内側ホーンを含み、全空間の quasicategory 性は不要。
使われ方：cofinality の引き戻しの安定性を弱飽和閉包へ移す生成元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：left fibration に沿う右ホーンの引き戻しは right cofinal。
方針：二段の固定した終点収縮を持ち上げ、共通 fiber からの消去則を使う。
規約：k ≠ 0。外側と内側を統一する。
使われ方：右ホーンの引き戻しの right anodyne 判定。 -/
lemma leftFibration_rightHorn_pullback_isRightCofinal {E : SSet.{u}}
    (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0)
    (p : E ⟶ (Δ[n + 1] : SSet.{u})) [LeftFibration p] :
    IsRightCofinal (pullback.fst p (horn (n + 1) k).ι) := by
  let f := (horn.{u} (n + 1) k).ι
  have : LeftFibration (pullback.snd p f) :=
    ⟨leftFibrations.pullback_snd p f (LeftFibration.mem (p := p))⟩
  apply isRightCofinal_pullback_fst_of_vertexFibers p f (cofinalRightHornVertex n k hk)
  · apply isRightCofinal_of_rightAnodyne
    exact leftFibration_terminalFiber_rightAnodyne_of_two_fixed_contractions _ _ _
      (cofinalRightHornRaise n k) (cofinalRightHornFinish n k hk)
      (cofinalRightHornRaise_zero n k) rfl (cofinalRightHornFinish_zero n k hk)
      (cofinalRightHornFinish_one n k hk) (cofinalRightHornRaise_const n k hk)
      (cofinalRightHornFinish_const n k hk)
  · exact leftFibration_terminalFiber_isRightCofinal p

/-- 概要：left fibration に沿う全ての右ホーンの引き戻しは right anodyne。
方針：証明した right cofinality と引き戻しの単射性による判定。
規約：内側ホーンも含む生成元ごとの定理。
使われ方：一般の right anodyne な射に拡張する弱飽和閉包の計算。 -/
lemma leftFibration_rightHorn_pullback_rightAnodyne {E : SSet.{u}}
    (n : ℕ) (k : Fin (n + 2)) (hk : k ≠ 0)
    (p : E ⟶ (Δ[n + 1] : SSet.{u})) [LeftFibration p] :
    rightAnodyneExtensions (pullback.fst p (horn (n + 1) k).ι) :=
  (leftFibration_rightHorn_pullback_isRightCofinal n k hk p).rightAnodyneExtensions

end SerrePositivity.InfinityCategories

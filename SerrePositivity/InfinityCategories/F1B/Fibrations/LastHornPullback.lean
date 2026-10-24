module

public import SerrePositivity.InfinityCategories.F1B.Fibrations.LastHornContraction
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexFiberBaseChange

/-!
概要：left fibration に沿う外側右ホーンの引き戻しは right anodyne。
方針：ホーンと標準単体の共通の終点 fiber の包含を比較し、cofinality の消去則を使う。
規約：内側ホーンを含む一般の right anodyne な射の安定性は後続の工程。
使われ方：Kerodon Proposition 7.2.3.10 のホーンへの還元の外側の場合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：引き戻し前後の対応する fiber の包含が right cofinal なら第一射影も right cofinal。
方針：fiber の底変換同型を合成に入れて、最初の因子の cofinality を消去する。
規約：fibration 性や単射性はこの一般補題には不要。
使われ方：底の終点収縮からホーンの引き戻しを比較する。 -/
lemma isRightCofinal_pullback_fst_of_vertexFibers {E A B : SSet.{u}}
    (p : E ⟶ B) (f : A ⟶ B) (a : A _⦋0⦌)
    (hq : IsRightCofinal (vertexFiberι (pullback.snd p f) a))
    (hp : IsRightCofinal (vertexFiberι p (f.app _ a))) :
    IsRightCofinal (pullback.fst p f) := by
  have he := isRightCofinal_of_rightAnodyne (cofinalVertexFiberBaseChangeIso p f a).hom
    (MorphismProperty.of_isIso rightAnodyneExtensions _)
  apply hq.cancel_left
  rw [← cofinalVertexFiberBaseChangeIso_hom_ι]
  exact he.comp hp

/-- 概要：left fibration に沿う外側右ホーンの引き戻しは right cofinal。
方針：二つの底で終点収縮を使い、同じ終点 fiber の包含から消去する。
規約：次元は n+1。全空間の quasicategory 性は要求しない。
使われ方：right anodyne な射の引き戻しの外側生成元。 -/
lemma leftFibration_lastHorn_pullback_isRightCofinal {E : SSet.{u}} (n : ℕ)
    (p : E ⟶ (Δ[n + 1] : SSet.{u})) [LeftFibration p] :
    IsRightCofinal (pullback.fst p (horn (n + 1) (Fin.last (n + 1))).ι) := by
  let f := (horn.{u} (n + 1) (Fin.last (n + 1))).ι
  have : LeftFibration (pullback.snd p f) :=
    ⟨leftFibrations.pullback_snd p f (LeftFibration.mem (p := p))⟩
  apply isRightCofinal_pullback_fst_of_vertexFibers p f (cofinalLastHornVertex n)
  · apply isRightCofinal_of_rightAnodyne
    exact leftFibration_terminalFiber_rightAnodyne_of_fixed_contraction _ _
      (cofinalLastHornContraction n) (cofinalLastHornContraction_zero n)
      (cofinalLastHornContraction_one n) (cofinalLastHornContraction_const n)
  · exact leftFibration_terminalFiber_isRightCofinal p

/-- 概要：left fibration に沿う外側右ホーンの引き戻しは right anodyne。
方針：引き戻しの単射性と証明した right cofinality から判定する。
規約：内側ホーンを含む全生成元の主張にはまだ拡張しない。
使われ方：Kerodon Proposition 7.2.3.10 の組合せ論的証明の外側の場合。 -/
lemma leftFibration_lastHorn_pullback_rightAnodyne {E : SSet.{u}} (n : ℕ)
    (p : E ⟶ (Δ[n + 1] : SSet.{u})) [LeftFibration p] :
    rightAnodyneExtensions (pullback.fst p (horn (n + 1) (Fin.last (n + 1))).ι) :=
  (leftFibration_lastHorn_pullback_isRightCofinal n p).rightAnodyneExtensions

end SerrePositivity.InfinityCategories

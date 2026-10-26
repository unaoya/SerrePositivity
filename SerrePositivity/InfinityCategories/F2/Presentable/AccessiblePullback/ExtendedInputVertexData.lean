module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.FinitePairSection

/-!
概要：元の二成分入力と追加入力を保つ厳密な頂点データをまとめる。
方針：同じ元の頂点と全成分値の等式を構造の各成分として保持する。
規約：データの存在は別途実際の構成で示す。
使われ方：相対交互構成と指定始点の下の余錐の回収の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：二成分族の元の引き戻し入力を同じ成分族へ射影する。
方針：元の二射影を二点の依存切断としてまとめる。
規約：零成分と一成分は元の射影に定義的に一致する。
使われ方：相対交互構成の共通入力。 -/
def pullbackComponentInput {K B : SSet.{u + 1}} {C : Fin 2 → SSet.{u + 1}}
    (p : ∀ c, C c ⟶ B) (a : K ⟶ pullback (p 0) (p 1)) : ∀ c, K ⟶ C c :=
  finitePairSection _ (a ≫ pullback.fst (p 0) (p 1)) (a ≫ pullback.snd (p 0) (p 1))

/-- 概要：元の引き戻しの全余錐を同じ二成分族へ射影する。
方針：元の二つの全後合成余錐を依存切断としてまとめる。
規約：元の全単体値を保持する。
使われ方：追加入力の固定標的を共通の入力に合わせる。 -/
def pullbackComponentInputCocone {K B : SSet.{u + 1}} {C : Fin 2 → SSet.{u + 1}}
    (p : ∀ c, C c ⟶ B) (a : K ⟶ pullback (p 0) (p 1)) (z : JoinCocone a) :
    ∀ c, JoinCocone (pullbackComponentInput p a c) :=
  finitePairSection _ (mapJoinCocone (pullback.fst (p 0) (p 1)) z)
    (mapJoinCocone (pullback.snd (p 0) (p 1)) z)

/-- 概要：追加入力を持つ両成分頂点と元の厳密な引き戻し頂点の全比較データ。
方針：compact 性と制限後の元の全成分値を別々の検証可能な成分にする。
規約：型は構成結果を記録し、その存在を仮定しない。
使われ方：元の compact 成分射影の under 試験余錐。 -/
structure ExtendedInputPullbackVertexData
    (μ : Cardinal.{u}) {K B : SSet.{u + 1}} [Quasicategory B]
    {C L : Fin 2 → SSet.{u + 1}} [∀ c, Quasicategory (C c)]
    (p : ∀ c, C c ⟶ B) (a : K ⟶ pullback (p 0) (p 1)) (z : JoinCocone a)
    (q : ∀ c, L c ⟶ C c) (i : ∀ c, K ⟶ L c)
    (hi : ∀ c, i c ≫ q c = pullbackComponentInput p a c)
    (zc : ∀ c, JoinCocone (q c))
    (hzi : ∀ c, joinMap (i c) (𝟙 Δ[0]) ≫ (zc c).val = (pullbackComponentInputCocone p a z c).val) where
  first : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder (q 0))).symm (zc 0))) _⦋0⦌
  second : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder (q 1))).symm (zc 1))) _⦋0⦌
  vertex : (sliceOver ((SSet.yonedaEquiv (X := sliceUnder a)).symm z)) _⦋0⦌
  compact : ComponentCompactVertex μ (p 0) (p 1)
    ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder a)).symm z) ≫
      sliceUnderProjection a).app (Opposite.op ⦋0⦌) vertex)
  first_value : vertex.val ≫ sliceUnderPostcomp a (pullback.fst (p 0) (p 1)) =
    ((stableInputRestriction (q 0) (i 0) (pullbackComponentInput p a 0) (hi 0) (zc 0)
      (pullbackComponentInputCocone p a z 0) (hzi 0)).app (Opposite.op ⦋0⦌) first).val
  second_value : vertex.val ≫ sliceUnderPostcomp a (pullback.snd (p 0) (p 1)) =
    ((stableInputRestriction (q 1) (i 1) (pullbackComponentInput p a 1) (hi 1) (zc 1)
      (pullbackComponentInputCocone p a z 1) (hzi 1)).app (Opposite.op ⦋0⦌) second).val

/-- 概要：構成済みの二成分比較を元の厳密な入力付き頂点データへ戻す。
方針：既存の追加入力付き貼り合わせの結果を同じ構造にまとめる。
規約：比較自体を入力に取る貼り合わせ補題。
使われ方：accessible 性から比較を構成した後の最後の厳密化。 -/
lemma nonempty_extendedInputPullbackVertexData_of_compatible
    (μ : Cardinal.{u}) {K B : SSet.{u + 1}} [Quasicategory B]
    {C L : Fin 2 → SSet.{u + 1}} [∀ c, Quasicategory (C c)]
    (p : ∀ c, C c ⟶ B) (a : K ⟶ pullback (p 0) (p 1)) (z : JoinCocone a)
    (q : ∀ c, L c ⟶ C c) (i : ∀ c, K ⟶ L c) [Mono (i 0)]
    (hi : ∀ c, i c ≫ q c = pullbackComponentInput p a c)
    (zc : ∀ c, JoinCocone (q c))
    (hzi : ∀ c, joinMap (i c) (𝟙 Δ[0]) ≫ (zc c).val = (pullbackComponentInputCocone p a z c).val)
    (hp : F1B.EquivalenceLifting (p 0))
    (hpr : ∀ c, pullbackComponentInput p a c ≫ p c = (a ≫ pullback.fst (p 0) (p 1)) ≫ p 0)
    (hzt : ∀ c, (pullbackComponentInputCocone p a z c).val ≫ p c =
      (mapJoinCocone (p 0) (mapJoinCocone (pullback.fst (p 0) (p 1)) z)).val)
    (v : ∀ c, (sliceOver ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (zc c))) _⦋0⦌)
    (hc : ∀ c, Compact.IsKappaCompact.{u, u + 1} μ
      ((sliceOverProjection ((SSet.yonedaEquiv (X := sliceUnder (q c))).symm (zc c)) ≫
        sliceUnderProjection (q c)).app (Opposite.op ⦋0⦌) (v c)))
    (he : VertexIso
      ((relativeInputPostcomp (q 0) (i 0) (pullbackComponentInput p a 0) (hi 0) (zc 0)
        (pullbackComponentInputCocone p a z 0) (hzi 0) (p 0)
        ((a ≫ pullback.fst (p 0) (p 1)) ≫ p 0) (hpr 0)
        (mapJoinCocone (p 0) (mapJoinCocone (pullback.fst (p 0) (p 1)) z)) (hzt 0)).app
          (Opposite.op ⦋0⦌) (v 0))
      ((relativeInputPostcomp (q 1) (i 1) (pullbackComponentInput p a 1) (hi 1) (zc 1)
        (pullbackComponentInputCocone p a z 1) (hzi 1) (p 1)
        ((a ≫ pullback.fst (p 0) (p 1)) ≫ p 0) (hpr 1)
        (mapJoinCocone (p 0) (mapJoinCocone (pullback.fst (p 0) (p 1)) z)) (hzt 1)).app
          (Opposite.op ⦋0⦌) (v 1))) :
    Nonempty (ExtendedInputPullbackVertexData μ p a z q i hi zc hzi) := by
  obtain ⟨dE, dD, w, hw, hF, hG⟩ :=
    exists_extendedInputPullbackVertex_of_compatible_components μ (p 0) (p 1) a z hp
      (q 0) (q 1) (i 0) (i 1) (hi 0) (hi 1) (zc 0) (zc 1) (hzi 0) (hzi 1) (hpr 1) (hzt 1)
        (v 0) (v 1) (hc 0) (hc 1) he
  exact ⟨⟨dE, dD, w, hw, hF, hG⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

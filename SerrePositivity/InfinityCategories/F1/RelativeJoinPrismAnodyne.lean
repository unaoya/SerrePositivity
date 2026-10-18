module

public import SerrePositivity.InfinityCategories.F1.RelativeJoinPrismCell
public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence

/-!
概要：prism の初期部分 Z(0) から最後の最大単体より前の Z(m) への inner anodyne 性。
方針：内側ホーンの pushout による各段階を自然数について有限合成する。
規約：モデル構造を使わず inner fibration に対する左持ち上げ性として結論する。
使われ方：Kerodon Lemma 3.1.2.12、Proposition 5.2.4.5 の比較の立方体。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：prism の零段階から m 以下の任意の段階への包含は inner anodyne。
方針：恒等射を基底とし、各段階の内側ホーンの pushout を有限合成する。
規約：最後の外側ホーンのセルを貼る m+1 段階を含めない。
使われ方：Kerodon Lemma 3.1.2.12、Z(0) から Z(m) への包含。 -/
lemma innerAnodyneExtensions_relativeJoinPrismStage (m r : ℕ) (hr : r ≤ m) :
    innerAnodyneExtensions (Subcomplex.homOfLE
      (relativeJoinPrismStage_monotone.{u} m (Nat.zero_le r))) := by
  induction r with
  | zero =>
    rw [Subcomplex.homOfLE_refl]
    exact innerAnodyneExtensions.of_isIso _
  | succ r ih =>
    have hi := ih (Nat.le_of_succ_le hr)
    let k : Fin (m + 1) := ⟨r, by omega⟩
    have hk : k < Fin.last m := by change r < m; omega
    have hs := innerAnodyneExtensions_relativeJoinPrismStage_step.{u} m k hk
    have he : Subcomplex.homOfLE (relativeJoinPrismStage_monotone.{u} m (Nat.zero_le (r + 1))) =
        Subcomplex.homOfLE (relativeJoinPrismStage_monotone m (Nat.zero_le r)) ≫
          Subcomplex.homOfLE (relativeJoinPrismStage_monotone m (Nat.le_succ r)) := rfl
    rw [he]
    exact innerAnodyneExtensions.comp_mem _ _ hi hs

/-- 概要：prism の初期部分から最後の最大単体を除く生成部分への包含は inner anodyne。
方針：零段階と m 段階をそれぞれ Z(0) と Z(m) と同定する。
規約：m=0 では恒等的な包含も含めて全次元で成立する。
使われ方：Kerodon Proposition 5.2.4.5、写像円柱比較の境界からの帰納に使う同値条件。 -/
lemma innerAnodyneExtensions_relativeJoinPrismInitial_penultimate (m : ℕ) :
    innerAnodyneExtensions (Subcomplex.homOfLE
      (relativeJoinPrismInitial_le_penultimate.{u} m)) := by
  let e₀ := Subcomplex.eqToIso (relativeJoinPrismStage_zero.{u} m)
  let eₘ := Subcomplex.eqToIso (relativeJoinPrismStage_penultimate.{u} m)
  have h := innerAnodyneExtensions_relativeJoinPrismStage.{u} m m le_rfl
  have hc := innerAnodyneExtensions.comp_mem _ _
    (innerAnodyneExtensions.comp_mem _ _ (innerAnodyneExtensions.of_isIso e₀.inv) h)
    (innerAnodyneExtensions.of_isIso eₘ.hom)
  exact hc

/-- 概要：Z(0) から Z(m) への包含は全 quasicategory への前合成の同値条件を満たす。
方針：inner anodyne 性を前合成の同値の一般判定に渡す。
規約：底や係数の追加の有限性を仮定せず全ての次元 m を扱う。
使われ方：Kerodon Proposition 5.2.4.5、写像円柱比較の立方体の一辺の同値条件。 -/
lemma isPrecompositionEquivalence_relativeJoinPrismInitial_penultimate (m : ℕ) :
    IsPrecompositionEquivalence (Subcomplex.homOfLE
      (relativeJoinPrismInitial_le_penultimate.{u} m)) :=
  isPrecompositionEquivalence_of_innerAnodyne _
    (innerAnodyneExtensions_relativeJoinPrismInitial_penultimate m)

end SerrePositivity.InfinityCategories

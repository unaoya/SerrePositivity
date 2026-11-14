module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Descent.NilpotentThickening
public import SerrePositivity.KST.Descent.ClosedDimension
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# 論文 §3 の幾何学的な基本補題

## 概要
軌道正方形・被約化・閉和で必要なスキーム補題のうち、Mathlib にあるものを公開する。

## 方針
有限射の固有性と被約な終域への全射閉埋め込みの同型性には既存証明を使う。
次元低下には既約閉集合の鎖を全空間まで一段伸ばす証明を使う。

## 規約
被約性は全射閉埋め込みの終域に要求する。
次元低下は有限な自然数上界、または実際の次元と自然数の等式を明示して使う。

## 使われ方
論文 補題 3.3、定理 3.1 の section の閉像・軌道正方形・被約化。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace SerrePositivity.KST.Descent

/-- 概要：有限射は固有（論文 補題 3.3・定理 3.1 の軌道正方形）。
方針：Mathlib の有限射から固有射への instance を使う。
規約：有限型・分離・普遍閉性を新しい公理として追加しない。
使われ方：strict transform と section の有限和から抽象 blowup を作る。 -/
theorem proper_of_finite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] : IsProper f :=
  inferInstance

/-- 概要：被約な終域への点全射閉埋め込みは同型（論文 定理 3.1）。
方針：核の台が全体なら被約性により核が零になる Mathlib の証明を使う。
規約：被約性を始域の仮定に取り違えない。
使われ方：相異なる section の像が互いに素になる開集合上の同型。 -/
theorem isIso_of_surjective_closedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [Surjective f] [IsReduced Y] : IsIso f :=
  AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective f

/-- 概要：被約な終域への冪零 thickening は同型（論文 §3 の被約化の比較）。
方針：核の冪零性から点全射性を証明し、全射閉埋め込みの同型性を使う。
規約：一般の被約化射が同型であるとは主張しない。
使われ方：被約化を戻す際の幾何学的な同型の確認。 -/
theorem nilpotentThickening_isIso_of_reduced {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsNilpotentThickening f] [IsReduced Y] : IsIso f := by
  have := nilpotentThickening_surjective f
  exact isIso_of_surjective_closedImmersion f

/-- 概要：分離射の切断は閉埋め込み（論文 定理 3.1 の section の軌道）。
方針：切断と構造射の合成が恒等射であり、分離射の前合成から閉埋め込み性が降りる。
規約：点集合の切断ではなく、スキームの射の切断。
使われ方：section の各 G 平行移動の閉像。 -/
theorem closedImmersion_of_section {X Y : Scheme.{u}} (p : X ⟶ Y) [IsSeparated p]
    (s : Y ⟶ X) (section_identity : s ≫ p = 𝟙 Y) : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ p) := by rw [section_identity]; infer_instance
  exact IsClosedImmersion.of_comp s p

/-- 概要：分離な対象への基底上の二射の等化子は閉埋め込み（論文 定理 3.1）。
方針：Mathlib の分離射の対角と引き戻しによる証明を使う。
規約：基底 S 上の等化子を使用する。
使われ方：二つの translated section の一致場所。 -/
theorem closedImmersion_equalizer {S : Scheme.{u}} {X Y : Over S}
    [IsSeparated Y.hom] (f g : X ⟶ Y) : IsClosedImmersion (equalizer.ι f g).left :=
  inferInstance

/-- 概要：被約な始域からの異なる二射の一致場所は真閉（論文 定理 3.1）。
方針：等化子が点全射なら被約性から同型となり、二射は一致してしまう。
規約：分離性は終域の構造射、被約性は始域に要求する。
使われ方：相異なる section の一致場所の和を真閉中心にする。 -/
theorem equalizer_range_ne_univ_of_ne {S : Scheme.{u}} {X Y : Over S}
    [IsReduced X.left] [IsSeparated Y.hom] (f g : X ⟶ Y) (hne : f ≠ g) :
    Set.range (equalizer.ι f g).left ≠ Set.univ := by
  intro hrange
  have : Surjective (equalizer.ι f g).left := ⟨Set.range_eq_univ.mp hrange⟩
  have : IsIso (equalizer.ι f g).left :=
    isIso_of_surjective_closedImmersion (equalizer.ι f g).left
  apply hne
  apply (Over.forget S).map_injective
  apply (cancel_epi (equalizer.ι f g).left).mp
  exact congrArg (fun k ↦ k.left) (equalizer.condition f g)

/-- 概要：有限次元の整スキームの真閉部分では次元が下がる（論文 §3、公理 (7)）。
方針：整スキームの既約性と、既約閉集合の鎖を一段伸ばす次元補題を使う。
規約：実際の次元と自然数 d の等式を明示し、無限次元の場合を含めない。
使われ方：補題 3.3 と定理 3.1 の真閉中心における次元帰納。 -/
theorem integral_properClosed_dimension_lt (X : Scheme.{u}) [IsIntegral X]
    (Z : Set X) (closed : IsClosed Z) (proper : Z ≠ Set.univ)
    (d : ℕ) (dimension : topologicalKrullDim X = d) :
    topologicalKrullDim Z < topologicalKrullDim X :=
  topologicalKrullDim_properClosed_lt Z closed proper d dimension

/-- 概要：有限次元上界を持つ既約な終域への真閉埋め込みでは次元が下がる（論文 §3）。
方針：始域を閉像との同相で比較し、真閉部分の次元低下を適用する。
規約：始域の被約性は不要で、実際の閉埋め込みを用いる。
使われ方：既約成分と残りの閉和の実際の交わりへの次元帰納。 -/
theorem closedImmersion_dimension_lt_bound {X Y : Scheme.{u}} [IrreducibleSpace Y]
    (f : X ⟶ Y) [IsClosedImmersion f] (proper : Set.range f ≠ Set.univ)
    (d : ℕ) (bound : topologicalKrullDim Y ≤ d) : topologicalKrullDim X < d := by
  calc
    topologicalKrullDim X = topologicalKrullDim (Set.range f) :=
      IsHomeomorph.topologicalKrullDim_eq _ f.isClosedEmbedding.toHomeomorph.isHomeomorph
    _ < d := topologicalKrullDim_properClosed_lt_bound (Set.range f)
      f.isClosedEmbedding.isClosed_range proper d bound

end SerrePositivity.KST.Descent

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite Paper "Proof step §3.3 geometry" (partial := component) "仮定：分離スキーム射の切断と、整な基底上の異なる切断の一致軌跡（原典の幾何の仮定）。結論：切断は閉埋め込みで、一致軌跡は真の閉集合（原典の幾何の一部。軌道和の被約化および L への作用は別）。"] _root_.SerrePositivity.KST.Descent.closedImmersion_equalizer
attribute [cite Paper "Proof step §3.3 geometry" (partial := component) "仮定：分離スキーム射の切断と、整な基底上の異なる切断の一致軌跡（原典の幾何の仮定）。結論：切断は閉埋め込みで、一致軌跡は真の閉集合（原典の幾何の一部。軌道和の被約化および L への作用は別）。"] _root_.SerrePositivity.KST.Descent.closedImmersion_of_section
attribute [cite Paper "Proof step §3.3 geometry" (partial := component) "仮定：分離スキーム射の切断と、整な基底上の異なる切断の一致軌跡（原典の幾何の仮定）。結論：切断は閉埋め込みで、一致軌跡は真の閉集合（原典の幾何の一部。軌道和の被約化および L への作用は別）。"] _root_.SerrePositivity.KST.Descent.equalizer_range_ne_univ_of_ne

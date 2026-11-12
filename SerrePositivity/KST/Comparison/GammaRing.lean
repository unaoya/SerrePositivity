module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWPreservation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWAssociativity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWPullback
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWUnitMap
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Alexander–Whitney 積による Γ の環構造

概要：dg 圏の自己 Hom の標準 Dold–Kan 模型に結合的環構造を入れる。
方針：既存 γ1.5 の AW の閉性・結合律・単位律を部分加群の環へまとめる。
規約：SS03 (2.9) の切断点による積。一般の dg 代数は一対象 dg 圏として扱う。
使われ方：KST §2.2、式 (2.2) の行列単体的モノイドの係数環。
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.KST.Comparison

open CategoryTheory DifferentialGraded


variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/--
概要：dg 自己 Hom の Γ の標準成分模型の各項。
方針：smart truncation の標準単体を使う。
規約：零次項は閉零元。SS03 §2.1、(2.2) の chain map 模型。
使われ方：SS03 (2.9) の AW 環と Mathlib Γ の同定。
-/
abbrev GammaEnd (x : D) (n : ℕ) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x x n

/--
概要：Γ の各次数の自己 Hom に AW 積の環構造を与える。
方針：切断点の和の結合律と双加法性、および dg 単位の定数単体を用いる。
規約：積 g*f は g が後の射となる SS03 (2.9) の通常順。
使われ方：KST 式 (2.2) の行列環の係数。
-/
instance gammaEndRing (x : D) (n : ℕ) : Ring (GammaEnd (R := R) x n) where
  toAddCommGroup := inferInstanceAs (AddCommGroup (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x x n))
  mul := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW
  one := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit x n
  mul_assoc a b c := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_assoc a.val b.val c.val).symm
  one_mul a := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_unit_left a.val)
  mul_one a := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_unit_right a.val)
  left_distrib a b c := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_add_right a.val b.val c.val)
  right_distrib a b c := Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_add_left a.val b.val c.val)
  zero_mul a := by
    apply Subtype.ext
    exact congrArg (fun f => f a.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDataBilinear x x x n).map_zero
  mul_zero a := by
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDataBilinear x x x n a.val).map_zero

/--
概要：全ての面・退化を環準同型として与える。
方針：既存の線形引き戻しに AW 積と定数単位の保存を添える。
規約：反変の単調写像で、SS03 (2.9) と可換な写像。
使われ方：Γ を単体的環としてまとめる。
-/
def gammaEndPullback (x : D) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) :
    GammaEnd (R := R) x n →+* GammaEnd (R := R) x m where
  __ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α).toAddMonoidHom
  map_one' := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardConstant_pullback (unitElement R x) α
  map_mul' a b := by
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW a b)).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α b)).val
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData a.val b.val) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α a).val (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α b).val
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_pullback α a.val b.val

/--
概要：自己 Hom の Dold–Kan 標準模型を単体的環として構成する。
方針：各次数の AW 環と、全ての単調写像に沿う環準同型をまとめる。
規約：SS03 (2.9) の環であり、可換性は要求しない。
使われ方：KST §2.2 の ĜL_n の入力。
-/
def gammaEndRingObject (x : D) : SimplicialObject RingCat.{u} where
  obj n := RingCat.of (GammaEnd (R := R) x n.unop.len)
  map f := RingCat.ofHom (gammaEndPullback x f.unop.toOrderHom)
  map_id n := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_id a
  map_comp f g := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_comp g.unop.toOrderHom f.unop.toOrderHom a).symm

/--
概要：Γ 環の加法的単体集合は既存の標準 Hom 空間である。
方針：定義を展開すると同じ台と引き戻しを得る。
規約：Mathlib Γ との比較は `standardDoldKanModuleIso` で与えられる。
使われ方：KST Lemma 2.13 のための Kan 性と π₀ の計算。
-/
theorem gammaEnd_underlying (x : D) :
    gammaEndRingObject (R := R) x ⋙ forget RingCat = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x x := rfl

/--
概要：AW 環の台単体集合は実際の Mathlib Γ と自然同型である。
方針：標準模型の加法的 Dold–Kan 同型を忘却関手で送る。
規約：乗法は SS03 (2.9) の成分模型で与え、Γ を単なる未証明入力にしない。
使われ方：KST §2.2 に用いる Γ の定義と smart truncation の接続。
-/
def gammaEndDoldKanIso (x : D) :
    gammaEndRingObject (R := R) x ⋙ forget RingCat ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := R) x x :=
  Functor.isoWhiskerRight (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardDoldKanModuleIso (R := R) x x) (forget (ModuleCat.{u} R))

end SerrePositivity.KST.Comparison

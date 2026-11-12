module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWPreservation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AWUnitMap

/-!
# 標準 Hom の単体的合成

概要：標準単体の AW 合成の単位則・結合律・自然性をまとめ、単体集合の合成写像を作る。
方針：成分族の既存の等式を部分型の外延性で標準単体に移す。
規約：豊穣順の入力は前の射 f、後の射 g とする。
使われ方：HA 1.3.1.13、Kerodon 2.5.8（Tag 00S0） の C_Δ の豊穣構造。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded MonoidalCategory
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

/-- 概要：標準単体の AW 合成は左単位則を満たす。
方針：成分族の単位則を部分型へ移す。
規約：単位は後の射の対象に置く。
使われ方：HA 1.3.1.13 の豊穣単位則。 -/
lemma standardAW_unit_left {x y : D} {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := R) y n) f = f :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_unit_left f.val)

/-- 概要：標準単体の AW 合成は右単位則を満たす。
方針：成分族の単位則を部分型へ移す。
規約：単位は前の射の対象に置く。
使われ方：HA 1.3.1.13 の豊穣単位則。 -/
lemma standardAW_unit_right {x y : D} {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardUnit (R := R) x n) = f :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_unit_right f.val)

/-- 概要：標準単体の AW 合成は結合律を満たす。
方針：成分族の結合律を部分型へ移す。
規約：通常順の合成の括弧付けを比較する。
使われ方：HA 1.3.1.13 の豊穣結合律。 -/
lemma standardAW_assoc {w x y z : D} {n : ℕ} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R y z n)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R w x n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW h (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW g f) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW h g) f :=
  Subtype.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_assoc h.val g.val f.val)

/-- 概要：標準単体の AW 合成は全ての引き戻しと可換である。
方針：標準引き戻しの台の計算と成分族の自然性を使う。
規約：面と退化をともに含む。
使われ方：Kerodon 2.5.8（Tag 00S0） の単体的合成の自然性。 -/
lemma standardAW_pullback {x y z : D} {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R y z n) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW g f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α g) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α f) := by
  apply Subtype.ext
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awData_pullback α g.val f.val

/-- 概要：標準 Hom の AW 合成を単体集合の射としてまとめる。
方針：各次数で二つの標準単体を合成し、引き戻しとの可換性を使う。
規約：第一因子が前の射、第二因子が後の射。
使われ方：HA 1.3.1.13 の豊穣合成。 -/
def standardComposition (x y z : D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) y z ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x z where
  app := fun _ ↦ ↾fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW s.2 s.1
  naturality := by
    intro m n α
    apply ConcreteCategory.hom_ext
    intro s
    exact (standardAW_pullback α.unop.toOrderHom s.2 s.1).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

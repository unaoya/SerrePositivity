module

public import SerrePositivity.InfinityCategories.DoldKanComparison.AWPreservation
public import SerrePositivity.InfinityCategories.DoldKanComparison.AWUnitMap

/-!
# 標準 Hom の単体的合成

概要：標準単体の AW 合成の単位則・結合律・自然性をまとめ、単体集合の合成写像を作る。
方針：成分族の既存の等式を部分型の外延性で標準単体に移す。
規約：豊穣順の入力は前の射 f、後の射 g とする。
使われ方：HA 1.3.1.13、Kerodon 2.5.8 の C_Δ の豊穣構造。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded DGNerve.PinchedHom MonoidalCategory
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：標準単体の AW 合成は左単位則を満たす。
方針：成分族の単位則を部分型へ移す。
規約：単位は後の射の対象に置く。
使われ方：HA 1.3.1.13 の豊穣単位則。 -/
lemma standardAW_unit_left {x y : D} {n : ℕ} (f : StandardSimplex R x y n) :
    standardAW (standardUnit (R := R) y n) f = f :=
  Subtype.ext (awData_unit_left f.val)

/-- 概要：標準単体の AW 合成は右単位則を満たす。
方針：成分族の単位則を部分型へ移す。
規約：単位は前の射の対象に置く。
使われ方：HA 1.3.1.13 の豊穣単位則。 -/
lemma standardAW_unit_right {x y : D} {n : ℕ} (f : StandardSimplex R x y n) :
    standardAW f (standardUnit (R := R) x n) = f :=
  Subtype.ext (awData_unit_right f.val)

/-- 概要：標準単体の AW 合成は結合律を満たす。
方針：成分族の結合律を部分型へ移す。
規約：通常順の合成の括弧付けを比較する。
使われ方：HA 1.3.1.13 の豊穣結合律。 -/
lemma standardAW_assoc {w x y z : D} {n : ℕ} (h : StandardSimplex R y z n)
    (g : StandardSimplex R x y n) (f : StandardSimplex R w x n) :
    standardAW h (standardAW g f) = standardAW (standardAW h g) f :=
  Subtype.ext (awData_assoc h.val g.val f.val)

/-- 概要：標準単体の AW 合成は全ての引き戻しと可換である。
方針：標準引き戻しの台の計算と成分族の自然性を使う。
規約：面と退化をともに含む。
使われ方：Kerodon 2.5.8 の単体的合成の自然性。 -/
lemma standardAW_pullback {x y z : D} {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (g : StandardSimplex R y z n) (f : StandardSimplex R x y n) :
    standardPullback α (standardAW g f) =
      standardAW (standardPullback α g) (standardPullback α f) := by
  apply Subtype.ext
  simp only [standardPullback_val, standardAW]
  exact awData_pullback α g.val f.val

/-- 概要：標準 Hom の AW 合成を単体集合の射としてまとめる。
方針：各次数で二つの標準単体を合成し、引き戻しとの可換性を使う。
規約：第一因子が前の射、第二因子が後の射。
使われ方：HA 1.3.1.13 の豊穣合成。 -/
def standardComposition (x y z : D) :
    standardHomSpace (R := R) x y ⊗ standardHomSpace (R := R) y z ⟶
      standardHomSpace (R := R) x z where
  app := fun _ ↦ ↾fun s ↦ standardAW s.2 s.1
  naturality := by
    intro m n α
    apply ConcreteCategory.hom_ext
    intro s
    exact (standardAW_pullback α.unop.toOrderHom s.2 s.1).symm

end SerrePositivity.InfinityCategories.DoldKanComparison

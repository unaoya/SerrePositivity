module

public import SerrePositivity.InfinityCategories.DoldKanComparison.AWUnit
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# 標準 Hom の単体的単位写像

概要：dg 単位の定数単体を全次数でまとめて単体集合の単位写像を作る。
方針：定数単体の引き戻しの自然性を使う。
規約：単体的圏の合成の構成に先立ち、単位の射のみを与える。
使われ方：HA 1.3.1.13、Kerodon 2.5.8 の C_Δ の豊穣単位。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DoldKanComparison

open CategoryTheory DifferentialGraded DGNerve.PinchedHom MonoidalCategory

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：閉零射の定数単体は全ての単調写像による引き戻しで保たれる。
方針：定数写像との合成が再び定数写像となることを使う。
規約：面と退化の両方を含める。
使われ方：Kerodon 2.5.8 の単位写像の単体的自然性。 -/
lemma standardConstant_pullback {x y : D} (z : zeroCycles (homObject R D x y))
    {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1)) :
    standardPullback α (standardConstant z n) = standardConstant z m := by
  unfold standardConstant
  rw [standardPullback_comp]
  rfl

/-- 概要：各次数で dg 単位の定数単体を取る。
方針：単位の閉零元を定数単体へ送る。
規約：全ての一点成分が同じ dg 単位である。
使われ方：HA 1.3.1.13 の単体的 Hom の単位。 -/
def standardUnit (x : D) (n : ℕ) : StandardSimplex R x x n :=
  standardConstant (unitElement R x) n

/-- 概要：dg 単位を標準 Hom へ送る単体集合の射を作る。
方針：各次数で定数の関数を取り、定数単体の引き戻しの自然性を使う。
規約：始域は SSet の cartesian monoidal 単位。
使われ方：HA 1.3.1.13 の C_Δ の豊穣単位写像。 -/
def standardUnitMap (x : D) : 𝟙_ SSet.{u} ⟶ standardHomSpace (R := R) x x where
  app := fun n ↦ ↾fun _ ↦ standardUnit (R := R) x n.unop.len
  naturality := by
    intro m n α
    apply ConcreteCategory.hom_ext
    intro s
    exact (standardConstant_pullback (unitElement R x) α.unop.toOrderHom).symm

end SerrePositivity.InfinityCategories.DoldKanComparison

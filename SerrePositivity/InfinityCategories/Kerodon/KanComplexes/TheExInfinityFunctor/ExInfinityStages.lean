module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExInfinity
public import Mathlib.AlgebraicTopology.SimplicialSet.Presentable

/-!
# Ex∞ の有限段階への因子化

概要：有限単体集合から Ex∞ への写像は有限反復を経由し、各段階の単位は余極限への射と整合する。
方針：有限表示可能性と順序余極限の余錐条件を使う。
規約：Moss 2020 Proposition 21 の有限段階から Kan 性への移行。
使われ方：horn を有限段階で充填して Ex∞ へ戻す。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Limits Opposite

/--
概要：有限単体集合から Ex∞ への写像は有限回の Ex の反復を経由する。
方針：有限単体集合の有限表示可能性による filtered colimit の因子化を使う。
規約：値の宇宙 u の有限表示可能性を、自然数添字の小さい余極限へ縮小して適用する。
使われ方：Ex∞ への horn の写像を有限段階へ持ち上げる。
-/
theorem exInfinity_finite_factorization (A X : SSet.{u}) [A.Finite]
    (f : A ⟶ exInfinity.obj X) :
    ∃ (m : ℕ) (g : A ⟶ (exIterate m).obj X), g ≫ (exInfinityStage m).app X = f := by
  let : PreservesFilteredColimitsOfSize.{0, 0} (coyoneda.obj (op A)) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits (coyoneda.obj (op A))
  exact Limits.exists_hom_of_preservesColimit_coyoneda (colimit.isColimit (exSequence.flip.obj X)) f

/--
概要：各反復の単位と次の段階から Ex∞ への射を合成すると元の段階の射になる。
方針：反復列の隣接する射を Ex の単位と同定して余極限の余錐条件を使う。
規約：Moss 2020 §3 の Ex∞ の遷移の規約。
使われ方：有限段階の充填の境界を Ex∞ で元の写像に戻す。
-/
@[reassoc] theorem exInfinityStage_succ (X : SSet.{u}) (m : ℕ) :
    exUnitAt ((exIterate m).obj X) ≫ (exInfinityStage (m + 1)).app X =
      (exInfinityStage m).app X := by
  have h : (exSequence.flip.obj X).map (homOfLE (Nat.le_add_right m 1)) =
      exUnitAt ((exIterate m).obj X) := by
    change (exSequence.map (homOfLE (Nat.le_add_right m 1))).app X = _
    simp only [exSequence, Functor.ofSequence_map_homOfLE_succ]
    rfl
  rw [← h]
  exact colimit.w (exSequence.flip.obj X) (homOfLE (Nat.le_add_right m 1))

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor

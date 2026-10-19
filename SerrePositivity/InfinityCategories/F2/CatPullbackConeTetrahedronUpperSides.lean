module

public import SerrePositivity.InfinityCategories.F2.CatPullbackConeTetrahedra
public import SerrePositivity.InfinityCategories.F2.ConeHomotopyTetrahedronUpperSides

/-!
概要：引き戻し錐の比較三単体の上側の側面。
方針：指定した錐と円柱の面の厳密な等式を使う。
規約：三角形や辺を新しく選択しない。
使われ方：三つの比較三単体の指定同型の合成関係。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

variable {A B C : SSet.{u}} [Quasicategory A] [Quasicategory B] [Quasicategory C]
/-- 概要：比較三単体の側面を対応する指定比較三角形に同定する。
方針：形状の元の射の始点・終点と円柱の側面の式を使う。
規約：二単体の厳密な等式を保持する。
使われ方：指定比較同型を四面の合成則へ代入する。 -/
lemma catPullbackConeTetrahedron_upper_long (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 2 (catPullbackConeTetrahedron p q f 0) =
      coneHomotopyUpperTriangle (catPullbackConeHomotopy p q)
        (ULift.up (ComposableArrows.mk₀ j)) := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))
  have hk : J.δ 0 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ j) := by
    apply ULift.ext
    exact (nerve.edgeMk f).tgt_eq
  exact (coneHomotopyTetrahedron_upper_long (catPullbackConeHomotopy p q) _).trans
    (congrArg (coneHomotopyUpperTriangle (catPullbackConeHomotopy p q)) hk)
/-- 概要：比較三単体の側面を対応する指定比較三角形に同定する。
方針：形状の元の射の始点・終点と円柱の側面の式を使う。
規約：二単体の厳密な等式を保持する。
使われ方：指定比較同型を四面の合成則へ代入する。 -/
lemma catPullbackConeTetrahedron_upper_first (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 3 (catPullbackConeTetrahedron p q f 0) =
      coneHomotopyUpperTriangle (catPullbackConeHomotopy p q)
        (ULift.up (ComposableArrows.mk₀ i)) := by
  let J := (SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan))
  have hk : J.δ 1 (ULift.up (nerve.edgeMk f).edge) = ULift.up (ComposableArrows.mk₀ i) := by
    apply ULift.ext
    exact (nerve.edgeMk f).src_eq
  exact (coneHomotopyTetrahedron_upper_first (catPullbackConeHomotopy p q) _).trans
    (congrArg (coneHomotopyUpperTriangle (catPullbackConeHomotopy p q)) hk)
/-- 概要：比較三単体の側面を対応する指定比較三角形に同定する。
方針：形状の元の射の始点・終点と円柱の側面の式を使う。
規約：二単体の厳密な等式を保持する。
使われ方：指定比較同型を四面の合成則へ代入する。 -/
lemma catPullbackConeTetrahedron_upper_last (p : A ⟶ C) (q : B ⟶ C)
    {i j : AsSmall.{u} WalkingCospan} (f : i ⟶ j) :
    CatInfinity.δ 0 (catPullbackConeTetrahedron p q f 1) =
      homotopyEdgeTriangleUpper (catPullbackConeHomotopy p q).h
        ((joinInr (Δ[0] : SSet.{u + 1})
          ((SSet.uliftFunctor.{u + 1, u}).obj (nerve (AsSmall.{u} WalkingCospan)))).app
            (Opposite.op ⦋1⦌) (ULift.up (nerve.edgeMk f).edge)) :=
  coneHomotopyTetrahedron_upper_last _ _

end SerrePositivity.InfinityCategories.F2

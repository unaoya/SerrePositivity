module

public import SerrePositivity.KST.Spectra.ExponentialHomotopyEdges
public import SerrePositivity.KST.Spectra.FibrationDifferenceTriangleLift

/-!
概要：共通の始点を持つ二つの実ホモトピーの終点を、指定三角形を保って比較する。
方針：指数写像空間の制限 fibration に、二辺固定の外二次元ホーン充填を適用する。
規約：底の二単体を選び直さない。使われ方：上下の指定三角形を保つ正方形の共有辺での比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.ExponentialPaths
variable {A B E : SSet.{u}} (i : B ⟶ A) {f g k : A ⟶ E}
  (H : SSet.Homotopy f g) (V : SSet.Homotopy f k)
  (D : (Δ[2] : SSet.{u}) ⟶ (ihom B).obj E)

/-- 元の二辺と指定した底の三角形全体を保つ、指数写像空間の実比較データ。 -/
structure SpecifiedDifference where
  edge : ((ihom A).obj E).Edge (vertex g) (vertex k)
  triangle : SSet.Edge.CompStruct (ExponentialPaths.edge H) edge (ExponentialPaths.edge V)
  triangle_over : SSet.yonedaEquiv.symm triangle.simplex ≫ (MonoidalClosed.pre i).app E = D

/-- 二つの実辺の射影が指定三角形の二辺なら、同じ三角形全体を保って終点を比較する。 -/
def SpecifiedDifference.choose [Mono i] [KanComplex E]
    (hH : curry H.h ≫ (MonoidalClosed.pre i).app E = stdSimplex.δ (2 : Fin 3) ≫ D)
    (hV : curry V.h ≫ (MonoidalClosed.pre i).app E = stdSimplex.δ (1 : Fin 3) ≫ D) :
    SpecifiedDifference i H V D := by
  let p := (MonoidalClosed.pre i).app E
  have hp : SSet.modelCategoryQuillen.J.rlp p :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance
  let hex := exists_difference_triangle_lift p hp (ExponentialPaths.edge H)
    (ExponentialPaths.edge V) D ((congrArg (· ≫ p) (edge_path H)).trans hH)
    ((congrArg (· ≫ p) (edge_path V)).trans hV)
  exact ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

/-- 比較後の新しい区間も、指定した同じ三角形の第二辺へ厳密に射影される。 -/
lemma SpecifiedDifference.edge_over (C : SpecifiedDifference i H V D) :
    SSet.yonedaEquiv.symm C.edge.edge ≫ (MonoidalClosed.pre i).app E =
      stdSimplex.δ (0 : Fin 3) ≫ D := by
  have h := congrArg (stdSimplex.δ (0 : Fin 3) ≫ ·) C.triangle_over
  rw [← Category.assoc, SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm] at h
  exact h

/-- 同じ比較辺を、元の射の間の実ホモトピーへ戻す。 -/
def SpecifiedDifference.homotopy (C : SpecifiedDifference i H V D) : SSet.Homotopy g k :=
  homotopyOfEdge C.edge

/-- 比較ホモトピーの指定部分上の全区間は、同じ底の対角辺を評価した族そのもの。 -/
lemma SpecifiedDifference.restriction (C : SpecifiedDifference i H V D) :
    i ▷ (Δ[1] : SSet.{u}) ≫ C.homotopy.h = uncurry (stdSimplex.δ (0 : Fin 3) ≫ D) := by
  change _ ≫ uncurry (SSet.yonedaEquiv.symm C.edge.edge) = _
  rw [← uncurry_pre_app, C.edge_over]

end SerrePositivity.KST.Spectra.ExponentialPaths

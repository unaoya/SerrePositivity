module

public import SerrePositivity.KST.Spectra.ExponentialHomotopyEdges
public import SerrePositivity.KST.Spectra.FibrationCodifferenceTriangleLift

/-!
概要：共通終点の二つの実ホモトピーの始点を、指定三角形を保って比較する。
方針：指数写像空間の制限 fibration に、同じ外二次元ホーンを相対充填する。
規約：底の二単体を保持。使われ方：実評価側と源単位側の指定境界付き比較。
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
  (H : SSet.Homotopy f k) (V : SSet.Homotopy g k)
  (D : (Δ[2] : SSet.{u}) ⟶ (ihom B).obj E)

/-- 元の二辺と底の三角形全体を保持する、共通終点の実比較データ。 -/
structure SpecifiedCodifference where
  edge : ((ihom A).obj E).Edge (vertex f) (vertex g)
  triangle : SSet.Edge.CompStruct edge (ExponentialPaths.edge V) (ExponentialPaths.edge H)
  triangle_over : SSet.yonedaEquiv.symm triangle.simplex ≫ (MonoidalClosed.pre i).app E = D

/-- 指定三角形の対角辺と第二辺を保持し、同じ三角形全体の上で始点を比較する。 -/
def SpecifiedCodifference.choose [Mono i] [KanComplex E]
    (hH : curry H.h ≫ (MonoidalClosed.pre i).app E = stdSimplex.δ (1 : Fin 3) ≫ D)
    (hV : curry V.h ≫ (MonoidalClosed.pre i).app E = stdSimplex.δ (0 : Fin 3) ≫ D) :
    SpecifiedCodifference i H V D := by
  let p := (MonoidalClosed.pre i).app E
  have hp : SSet.modelCategoryQuillen.J.rlp p :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance
  let hex := exists_codifference_triangle_lift p hp (ExponentialPaths.edge H)
    (ExponentialPaths.edge V) D ((congrArg (· ≫ p) (edge_path H)).trans hH)
    ((congrArg (· ≫ p) (edge_path V)).trans hV)
  exact ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

/-- 新しい比較区間の射影も、指定した同じ三角形の第一辺そのもの。 -/
lemma SpecifiedCodifference.edge_over (C : SpecifiedCodifference i H V D) :
    SSet.yonedaEquiv.symm C.edge.edge ≫ (MonoidalClosed.pre i).app E =
      stdSimplex.δ (2 : Fin 3) ≫ D := by
  have h := congrArg (stdSimplex.δ (2 : Fin 3) ≫ ·) C.triangle_over
  rw [← Category.assoc, SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm] at h
  exact h

/-- 同じ比較辺を元の二つの始点の間の実ホモトピーへ戻す。 -/
def SpecifiedCodifference.homotopy (C : SpecifiedCodifference i H V D) : SSet.Homotopy f g :=
  homotopyOfEdge C.edge

/-- 指定部分上の全区間は、保存した同じ底の第一辺の評価に厳密一致。 -/
lemma SpecifiedCodifference.restriction (C : SpecifiedCodifference i H V D) :
    i ▷ (Δ[1] : SSet.{u}) ≫ C.homotopy.h = uncurry (stdSimplex.δ (2 : Fin 3) ≫ D) := by
  change _ ≫ uncurry (SSet.yonedaEquiv.symm C.edge.edge) = _
  rw [← uncurry_pre_app, C.edge_over]

end SerrePositivity.KST.Spectra.ExponentialPaths

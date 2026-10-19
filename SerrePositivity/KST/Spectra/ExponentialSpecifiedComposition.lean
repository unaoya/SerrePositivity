module

public import SerrePositivity.KST.Spectra.ExponentialHomotopyEdges

/-!
概要：二つの実ホモトピーを、指定部分上の実合成三角形を保って貼り合わせる。
方針：指数写像空間の制限 fibration に、二辺固定の内二次元ホーン充填を適用する。
規約：底の二単体を選び直さない。使われ方：上下の指定三角形を保つ正方形の合成。
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
  (H : SSet.Homotopy f g) (V : SSet.Homotopy g k)
  (D : (Δ[2] : SSet.{u}) ⟶ (ihom B).obj E)

/-- 元の二辺と指定した底の三角形全体を保つ、指数写像空間の実合成データ。 -/
structure SpecifiedComposite where
  edge : ((ihom A).obj E).Edge (vertex f) (vertex k)
  triangle : SSet.Edge.CompStruct (ExponentialPaths.edge H) (ExponentialPaths.edge V) edge
  triangle_over : SSet.yonedaEquiv.symm triangle.simplex ≫ (MonoidalClosed.pre i).app E = D

/-- 二つの実辺の射影が指定三角形の二辺なら、同じ三角形全体を保って合成する。 -/
def SpecifiedComposite.choose [Mono i] [KanComplex E]
    (hH : curry H.h ≫ (MonoidalClosed.pre i).app E = stdSimplex.δ (2 : Fin 3) ≫ D)
    (hV : curry V.h ≫ (MonoidalClosed.pre i).app E = stdSimplex.δ (0 : Fin 3) ≫ D) :
    SpecifiedComposite i H V D := by
  let p := (MonoidalClosed.pre i).app E
  have hp : SSet.modelCategoryQuillen.J.rlp p := (fibration_iff _).1 inferInstance
  let hex := exists_composition_triangle_lift p hp (ExponentialPaths.edge H)
    (ExponentialPaths.edge V) D ((congrArg (· ≫ p) (edge_path H)).trans hH)
    ((congrArg (· ≫ p) (edge_path V)).trans hV)
  exact ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec⟩

/-- 合成後の対角区間も、指定した同じ三角形の対角辺へ厳密に射影される。 -/
lemma SpecifiedComposite.edge_over (C : SpecifiedComposite i H V D) :
    SSet.yonedaEquiv.symm C.edge.edge ≫ (MonoidalClosed.pre i).app E =
      stdSimplex.δ (1 : Fin 3) ≫ D := by
  have h := congrArg (stdSimplex.δ (1 : Fin 3) ≫ ·) C.triangle_over
  rw [← Category.assoc, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm] at h
  exact h

/-- 同じ合成辺を、元の射の間の実ホモトピーへ戻す。 -/
def SpecifiedComposite.homotopy (C : SpecifiedComposite i H V D) : SSet.Homotopy f k :=
  homotopyOfEdge C.edge

/-- 合成ホモトピーの指定部分上の全区間は、同じ底の対角辺を評価した族そのもの。 -/
lemma SpecifiedComposite.restriction (C : SpecifiedComposite i H V D) :
    i ▷ (Δ[1] : SSet.{u}) ≫ C.homotopy.h = uncurry (stdSimplex.δ (1 : Fin 3) ≫ D) := by
  change _ ≫ uncurry (SSet.yonedaEquiv.symm C.edge.edge) = _
  rw [← uncurry_pre_app, C.edge_over]

end SerrePositivity.KST.Spectra.ExponentialPaths

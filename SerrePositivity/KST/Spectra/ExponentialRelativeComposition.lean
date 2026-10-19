module

public import SerrePositivity.KST.Spectra.ExponentialHomotopyEdges

/-!
概要：後半が指定部分を固定する二つの実ホモトピーを、前半の射影を厳密に保って合成する。
方針：源の制限 fibration 上で退化三角形へ持ち上げ、元の実辺と合成二単体を保持する。
規約：指定部分で前半が非定数でもよい。使われ方：三辺を保持する正方形の右辺修正。
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

/-- 二つの元の実辺、同じ合成三角形、指定した前半の射影を持つ合成データ。 -/
structure RelativeComposite where
  edge : ((ihom A).obj E).Edge (vertex f) (vertex k)
  triangle : SSet.Edge.CompStruct (ExponentialPaths.edge H) (ExponentialPaths.edge V) edge
  edge_over : SSet.yonedaEquiv.symm edge.edge ≫ (MonoidalClosed.pre i).app E =
    curry H.h ≫ (MonoidalClosed.pre i).app E
  triangle_over : SSet.yonedaEquiv.symm triangle.simplex ≫ (MonoidalClosed.pre i).app E =
    SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.compId
      ((ExponentialPaths.edge H).map ((MonoidalClosed.pre i).app E))).simplex

/-- 後半の射影が定数なら、前半の指定射影と三角形全体を保つ実合成を構成する。 -/
def RelativeComposite.choose [Mono i] [KanComplex E]
    (hV : i ▷ (Δ[1] : SSet.{u}) ≫ V.h =
      fst B (Δ[1] : SSet.{u}) ≫ i ≫ g) : RelativeComposite i H V := by
  let p := (MonoidalClosed.pre i).app E
  have hp : SSet.modelCategoryQuillen.J.rlp p := (fibration_iff _).1 inferInstance
  let r := (ExponentialPaths.edge H).map p
  have hr : SSet.yonedaEquiv.symm r.edge = curry H.h ≫ p := by
    rw [SSet.Edge.map_edge, ← SSet.yonedaEquiv_symm_comp, edge_path]
  have hg : SSet.yonedaEquiv.symm (ExponentialPaths.edge V).edge ≫ p =
      SSet.const (p.app _ (vertex g)) := by
    rw [edge_path_pre, hV, curry_fst, vertex_pre]
  let hex := exists_edge_composite_over_path p hp (ExponentialPaths.edge H)
    (ExponentialPaths.edge V) r ((edge_path H ▸ hr).symm) hg
  exact ⟨hex.choose, hex.choose_spec.choose, hex.choose_spec.choose_spec.1.trans hr,
    hex.choose_spec.choose_spec.2⟩

/-- 選んだ同じ指数辺を、元の二つの射の間の実ホモトピーへ戻す。 -/
def RelativeComposite.homotopy (C : RelativeComposite i H V) : SSet.Homotopy f k :=
  homotopyOfEdge C.edge

/-- 合成後も、指定部分上の全区間は元の前半ホモトピーそのもの。 -/
lemma RelativeComposite.restriction (C : RelativeComposite i H V) :
    i ▷ (Δ[1] : SSet.{u}) ≫ C.homotopy.h = i ▷ (Δ[1] : SSet.{u}) ≫ H.h := by
  change _ ≫ uncurry (SSet.yonedaEquiv.symm C.edge.edge) = _
  rw [← uncurry_pre_app, C.edge_over, uncurry_pre_app, uncurry_curry]

end SerrePositivity.KST.Spectra.ExponentialPaths

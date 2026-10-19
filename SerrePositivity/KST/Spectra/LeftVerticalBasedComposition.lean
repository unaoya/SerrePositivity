module

public import SerrePositivity.KST.Spectra.PointedBasedPathComposition
public import SerrePositivity.KST.Spectra.FibrationCompositionTriangleLift
public import SerrePositivity.KST.Spectra.IdentityTriangleHomotopy

/-!
概要：第一辺が垂直な二つの実区間を、第二辺の射影トレースを保って合成する。
方針：底に恒等辺と第二辺の同じトレースの退化三角形を指定して内ホーンを充填する。
規約：元の二辺を保持する。使われ方：BF 単位までの全 Hom 区間の余分な射影選択を除く。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping
variable {T E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g h : T ⟶ E}
  (P : VerticalPath p f g) (Q : VerticalPath (PointedObject.toPoint E) g h)

/-- 同じ二辺の合成と、第二辺の同じ射影トレースを持つ退化三角形の厳密な持ち上げ。 -/
structure LeftVerticalBasedComposite where
  composite : BasedPathComposite P.forgetProjection Q
  triangle_over : SSet.yonedaEquiv.symm composite.triangle.simplex ≫
    (PointedObject.basedHomMap T p).right =
    SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp
      (Q.edge.map (PointedObject.basedHomMap T p).right)).simplex

/-- 底の退化三角形全体を指定し、二辺固定の内ホーン充填で合成する。 -/
def LeftVerticalBasedComposite.choose (hp : SSet.modelCategoryQuillen.J.rlp p.right) :
    LeftVerticalBasedComposite P Q := by
  letI baseFibration : Fibration p.right := (SSet.modelCategoryQuillen.fibration_iff _).2 hp
  letI postFibration : Fibration (PointedObject.basedHomMap T p).right := post_fibration T p
  let r := (PointedObject.basedHomMap T p).right
  let D := SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.idComp (Q.edge.map r)).simplex
  have hP : SSet.yonedaEquiv.symm P.edge.edge ≫ r = stdSimplex.δ (2 : Fin 3) ≫ D := by
    change SSet.yonedaEquiv.symm (SSet.yonedaEquiv P.path) ≫ r = _
    rw [Equiv.symm_apply_apply]
    dsimp only [D]
    rw [SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm, edgeId_yonedaEquiv_symm]
    rw [P.over, familyVertex_post, P.endpoint_over]
  have hQ : SSet.yonedaEquiv.symm Q.edge.edge ≫ r = stdSimplex.δ (0 : Fin 3) ≫ D := by
    dsimp only [D]
    rw [SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm, SSet.Edge.map_edge]
    exact SSet.yonedaEquiv_symm_comp Q.edge.edge r
  let hex := exists_composition_triangle_lift r
    ((SSet.modelCategoryQuillen.fibration_iff _).1 postFibration) P.edge Q.edge D hP hQ
  let e := hex.choose
  let t := hex.choose_spec.choose
  let R := basedPathOfEdge e
  have he : e.edge = R.edge.edge :=
    (congrArg (fun a => a.edge) (basedPathOfEdge_edge e)).symm
  let tri : SSet.Edge.CompStruct P.forgetProjection.edge Q.edge R.edge :=
    { simplex := t.simplex, d₂ := t.d₂, d₀ := t.d₀, d₁ := t.d₁.trans he }
  exact ⟨⟨R, tri⟩, hex.choose_spec.choose_spec⟩

/-- 合成対角辺の射影は、同じ第二辺の射影トレースそのもの。 -/
lemma LeftVerticalBasedComposite.path_over (C : LeftVerticalBasedComposite P Q) :
    C.composite.path.path ≫ (PointedObject.basedHomMap T p).right =
      Q.path ≫ (PointedObject.basedHomMap T p).right := by
  have he := congrArg (stdSimplex.δ (1 : Fin 3) ≫ ·) C.triangle_over
  rw [← Category.assoc, SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm,
    SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm, SSet.Edge.map_edge,
    ← SSet.yonedaEquiv_symm_comp] at he
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv C.composite.path.path) ≫ _ =
    SSet.yonedaEquiv.symm (SSet.yonedaEquiv Q.path) ≫ _ at he
  simpa only [Equiv.symm_apply_apply] using he

/-- 元の全パラメータを評価しても、合成対角区間の射影は第二辺の同じ実トレース。 -/
lemma LeftVerticalBasedComposite.homotopy_over (C : LeftVerticalBasedComposite P Q) :
    C.composite.path.homotopy.h ≫ p.right = Q.homotopy.h ≫ p.right := by
  have he := congrArg (fun F => MonoidalClosed.uncurry
    (F ≫ PointedObject.basedHomι T B)) C.path_over
  have he' : (C.composite.path.basedPost p).homotopy.h = (Q.basedPost p).homotopy.h := by
    rw [VerticalPath.homotopy_h, VerticalPath.homotopy_h]
    exact he
  simpa only [VerticalPath.basedPost_homotopy_h] using he'

end SerrePositivity.KST.Spectra.PointedMapping

module
public import SerrePositivity.KST.SConstruction.KanFibrationTriangleLifting
public import SerrePositivity.KST.SConstruction.KanSpanPastingChoices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FixedDiagramHomotopy

/-! # 変化する二円柱の指定境界三角形を保つ相対合成
概要：二脚自体が変わる場合に、元の二円柱と指定した境界の実三角形を全次数で保持する。
方針：関手空間の制限 fibration に沿って一つの外側三角形を持ち上げる。
規約：境界の逆三角形は要求せず、指定比較辺と一つの三角形だけを厳密に回収する。
使われ方：高次入力の二円柱族から、既存 BF 境界を保つ実適合円柱を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {T U E : SSet.{u}} [KanComplex E] (j : T ⟶ U) [Mono j]
  {D F G : U ⟶ E} (a : SSet.Homotopy D F) (b : SSet.Homotopy D G)
  (e : ((ihom T).obj E).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ G)))
  (t : SSet.Edge.CompStruct
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)).map ((pre j).app E)) e
    ((SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)).map ((pre j).app E)))

/-- 元の二円柱と指定境界の比較辺・実二単体を全パラメータで厳密に保持する合成。 -/
def relativeKanOuterSpanFamilyData :
    {g : ((ihom U).obj E).Edge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) //
      ∃ s : SSet.Edge.CompStruct
        (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a)) g
        (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)),
        ((pre j).app E).app (Opposite.op ⦋1⦌) g.edge = e.edge ∧
        ((pre j).app E).app (Opposite.op ⦋2⦌) s.simplex = t.simplex} := by
  let : Fibration ((pre j).app E) := inferInstance
  let hex := exists_kanFibration_liftOuterTriangle ((pre j).app E)
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a))
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)) e t
  exact ⟨hex.choose, hex.choose_spec.choose,
    hex.choose_spec.choose_spec.2, hex.choose_spec.choose_spec.1⟩

/-- 元の二脚の全パラメータの相対比較ホモトピー。 -/
def relativeKanOuterSpanComposite : SSet.Homotopy F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge (relativeKanOuterSpanFamilyData j a b e t).val.toTruncated

/-- 相対合成の実円柱は、指定した元の境界比較辺の実円柱を厳密に回収する。 -/
lemma relativeKanOuterSpanComposite_boundary :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (relativeKanOuterSpanComposite j a b e t).h =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyOfFunctorEdge e.toTruncated).h := by
  change (j ▷ (Δ[1] : SSet.{u})) ≫ uncurry
    (SSet.yonedaEquiv.symm (relativeKanOuterSpanFamilyData j a b e t).val.edge) =
      uncurry (SSet.yonedaEquiv.symm e.edge)
  rw [← uncurry_pre_app, SSet.yonedaEquiv_symm_comp,
    (relativeKanOuterSpanFamilyData j a b e t).property.choose_spec.1]

/-- 指定境界の比較辺が恒等なら、元の全パラメータの比較円柱は境界上で定数。 -/
lemma relativeKanOuterSpanComposite_boundary_constant
    (he : e.edge = (SSet.Edge.id (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (j ≫ F))).edge) :
    (j ▷ (Δ[1] : SSet.{u})) ≫ (relativeKanOuterSpanComposite j a b e t).h =
      fst T Δ[1] ≫ j ≫ F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.simplicialHomotopyOfFunctorEdge_pre_eq_constant j (j ≫ F)
    (relativeKanOuterSpanFamilyData j a b e t).val.toTruncated
    ((relativeKanOuterSpanFamilyData j a b e t).property.choose_spec.1.trans he)

/-- 相対合成の同じ比較辺と元の二脚を持つ、持ち上げた実三角形。 -/
def relativeKanOuterSpanTriangle : SSet.Edge.CompStruct
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy a))
    (relativeKanOuterSpanFamilyData j a b e t).val
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy b)) :=
  (relativeKanOuterSpanFamilyData j a b e t).property.choose

/-- 相対合成の同じ選択から取り出す、実際の全パラメータの二単体族。 -/
def relativeKanOuterSpanTriangleFamily : U ⊗ (Δ[2] : SSet.{u}) ⟶ E :=
  uncurry (SSet.yonedaEquiv.symm (relativeKanOuterSpanTriangle j a b e t).simplex)

/-- 同じ実二単体族は、境界で元の指定した実三角形族そのものを回収する。 -/
lemma relativeKanOuterSpanTriangleFamily_boundary :
    (j ▷ (Δ[2] : SSet.{u})) ≫ relativeKanOuterSpanTriangleFamily j a b e t =
      uncurry (SSet.yonedaEquiv.symm t.simplex) := by
  rw [relativeKanOuterSpanTriangleFamily, ← uncurry_pre_app, SSet.yonedaEquiv_symm_comp]
  change uncurry (SSet.yonedaEquiv.symm
    (((pre j).app E).app (Opposite.op ⦋2⦌)
      (relativeKanOuterSpanFamilyData j a b e t).property.choose.simplex)) = _
  rw [(relativeKanOuterSpanFamilyData j a b e t).property.choose_spec.2]

/-- 全実二単体族の第一面は、元の変化する第一円柱そのもの。 -/
lemma relativeKanOuterSpanTriangleFamily_source :
    (U ◁ stdSimplex.δ 2) ≫ relativeKanOuterSpanTriangleFamily j a b e t = a.h := by
  rw [relativeKanOuterSpanTriangleFamily, ← uncurry_natural_left,
    stdSimplex.δ_comp_yonedaEquiv_symm, (relativeKanOuterSpanTriangle j a b e t).d₂]
  change uncurry (curry a.h) = _
  exact uncurry_curry _

/-- 全実二単体族の第二面も、元の変化する第二円柱そのもの。 -/
lemma relativeKanOuterSpanTriangleFamily_target :
    (U ◁ stdSimplex.δ 1) ≫ relativeKanOuterSpanTriangleFamily j a b e t = b.h := by
  rw [relativeKanOuterSpanTriangleFamily, ← uncurry_natural_left,
    stdSimplex.δ_comp_yonedaEquiv_symm, (relativeKanOuterSpanTriangle j a b e t).d₁]
  change uncurry (curry b.h) = _
  exact uncurry_curry _

/-- 全実二単体族の残りの面は、同じ選択から作った相対比較円柱そのもの。 -/
lemma relativeKanOuterSpanTriangleFamily_composite :
    (U ◁ stdSimplex.δ 0) ≫ relativeKanOuterSpanTriangleFamily j a b e t =
      (relativeKanOuterSpanComposite j a b e t).h := by
  rw [relativeKanOuterSpanTriangleFamily, ← uncurry_natural_left,
    stdSimplex.δ_comp_yonedaEquiv_symm, (relativeKanOuterSpanTriangle j a b e t).d₀]
  rfl

end SerrePositivity.KST.SConstruction

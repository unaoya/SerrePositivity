module

public import SerrePositivity.InfinityCategories.F2.Presentable.HomComparison
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningSimplexRestriction
public import SerrePositivity.InfinityCategories.F1.Coherent.EnrichedHomotopy

/-!
概要：底上の全空間比較の分類は恒等・合成と相対 Hom 内の同型を保つ。
方針：元の coherent nerve の辺の法則を分類関手で送り、端点の等式の共役を相殺する。
規約：分類比較の元の射を保持する。
使われ方：解関手の全自然な retract の分裂三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：分類比較は元の底上の恒等射を恒等変換へ送る。
方針：coherent nerve の恒等辺と端点の共役の式を使う。
規約：元の全分類図式の恒等射。
使われ方：分類した分裂三角形の恒等辺の回収。 -/
lemma leftClassificationHom_id {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [LeftFibration p] :
    leftClassificationHom p p (𝟙 E) (Category.id_comp p) = 𝟙 _ := by
  have he : leftFibrationInfinityEdge p p (𝟙 E) (Category.id_comp p) =
      SSet.Edge.id (leftFibrationInfinityVertex p) := by
    exact coherentNerveEdge_id (leftFibrationObjectOf p)
  unfold leftClassificationHom
  rw [he, SSet.Edge.map_id]
  have hid {X : SSet.{u + 1}} {x y : X _⦋0⦌} (h : x = y) :
      (SSet.Edge.id x).ofEq h h = SSet.Edge.id y := by
    cases h
    rfl
  dsimp only
  rw [hid]
  exact SSet.Truncated.HomotopyCategory.homMk_id _

/-- 概要：元の底上の合成の分類は、二つの全分類比較の合成に一致する。
方針：元の coherent な合成三角形を分類し、端点を同じ全分類図式へ合わせる。
規約：元の合成射 f ≫ g を保持する。
使われ方：分類した retract の分裂等式。 -/
lemma leftClassificationHom_comp {E H J B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) (r : J ⟶ B)
    [LeftFibration p] [LeftFibration q] [LeftFibration r]
    (f : E ⟶ H) (hf : f ≫ q = p) (g : H ⟶ J) (hg : g ≫ r = q) :
    leftClassificationHom p q f hf ≫ leftClassificationHom q r g hg =
      leftClassificationHom p r (f ≫ g) (by rw [Category.assoc, hg, hf]) := by
  let f₀ : leftFibrationObjectOf p ⟶ leftFibrationObjectOf q := Over.homMk f hf
  let g₀ : leftFibrationObjectOf q ⟶ leftFibrationObjectOf r := Over.homMk g hg
  let S := leftStraighteningInfinityMap B
  let e₀₁ := (coherentNerveEdge f₀).map S
  let e₁₂ := (coherentNerveEdge g₀).map S
  let e₀₂ := (coherentNerveEdge (f₀ ≫ g₀)).map S
  let ep := (leftStraighteningInfinityDiagram_vertex p).symm
  let eq := (leftStraighteningInfinityDiagram_vertex q).symm
  let er := (leftStraighteningInfinityDiagram_vertex r).symm
  have t : SSet.Edge.CompStruct (e₀₁.ofEq ep eq) (e₁₂.ofEq eq er) (e₀₂.ofEq ep er) :=
    ((coherentNerveCompStruct f₀ g₀).map S).ofEq rfl rfl rfl
  exact SSet.Truncated.HomotopyCategory.homMk_comp_homMk t.toTruncated

/-- 概要：相対関手空間で同型な二つの全空間比較は同じ全分類射を与える。
方針：元の豊穣 Hom の同型を coherent nerve の辺の同値類へ送り、分類する。
規約：同じ底と両端の全空間を固定する。
使われ方：解錐が与える相対ホモトピーから分裂等式を導く。 -/
lemma leftClassificationHom_eq_of_relativeVertexIso
    {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f g : E ⟶ H) (hf : f ≫ q = p) (hg : g ≫ q = p)
    (h : VertexIso (relativeFunctorVertex q p f hf) (relativeFunctorVertex q p g hg)) :
    leftClassificationHom p q f hf = leftClassificationHom p q g hg := by
  let f₀ : leftFibrationObjectOf p ⟶ leftFibrationObjectOf q := Over.homMk f hf
  let g₀ : leftFibrationObjectOf p ⟶ leftFibrationObjectOf q := Over.homMk g hg
  have h₀ : VertexIso
      (SimplicialCategory.homEquiv' (leftFibrationObjectOf p) (leftFibrationObjectOf q) f₀)
      (SimplicialCategory.homEquiv' (leftFibrationObjectOf p) (leftFibrationObjectOf q) g₀) := h
  have he := coherentNerveEdge_homMk_eq_of_enrichedVertexIso h₀
  have hm := congrArg ((hoFunctor.map (leftStraighteningInfinityMap B)).toFunctor.map) he
  unfold leftClassificationHom
  rw [homMk_edge_ofEq, homMk_edge_ofEq]
  exact congrArg (fun k ↦ eqToHom _ ≫ k ≫ eqToHom _) hm

end SerrePositivity.InfinityCategories.F2.Presentable

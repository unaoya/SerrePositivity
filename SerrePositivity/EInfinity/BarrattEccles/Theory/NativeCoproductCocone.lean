module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.CAlgCoproductFunctor
public import SerrePositivity.EInfinity.SimplicialLocalization.FreeHammockArrowPoint
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoconeEdges
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductCocone
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Edges

/-!
# 指定された二項余積の native な余錐

## 概要
HA 3.2.4.7 の余積関手の同じ頂点と、厳密な二つの包含を持つ余錐を構成する。

## 方針
cofibrant な代表の余積包含を DK の元の生成射へ送り、その二本の辺を貼る。

## 規約
ここでは余錐とその脚・頂点を構成する。余極限性は次の比較で検査する。

## 使われ方
coprodWith_cocone の供給と、指定 Hopf 比較の二脚の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories SimplicialLocalization
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A]

/-- 元の cofibrant 代数の射を、同じ DK 頂点の間の辺へ送る。 -/
def cAlgCofibrantArrow {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y) :
    (CAlg_R A).Edge (cAlgVertexEquiv A X) (cAlgVertexEquiv A Y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((eHomEquiv SSet.{u + 1}).symm
    (localizationArrowPoint (cofibrantAlgebraRelativeCategory A) f ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _))

/-- 同じ cofibrant な厳密余積の、第一の指定包含。 -/
def cofibrantAlgebraDKCoprodInl (X Y : CofibrantAlgebra A) :
    (show (cofibrantAlgebraRelativeCategory A).category from X) ⟶
      (cofibrantAlgebraDKCoprodWith A Y).obj X := by
  let := modelCategory A
  exact ULift.up (ObjectProperty.homMk (coprod.inl : X.obj ⟶ X.obj ⨿ Y.obj))

/-- 同じ cofibrant な厳密余積の、第二の指定包含。 -/
def cofibrantAlgebraDKCoprodInr (X Y : CofibrantAlgebra A) :
    (show (cofibrantAlgebraRelativeCategory A).category from Y) ⟶
      (cofibrantAlgebraDKCoprodWith A Y).obj X := by
  let := modelCategory A
  exact ULift.up (ObjectProperty.homMk (coprod.inr : Y.obj ⟶ X.obj ⨿ Y.obj))

/-- 指定した二つの頂点の cofibrant 代表の、同じ余積の頂点。 -/
def cAlgCoprodVertex (x y : (CAlg_R A) _⦋0⦌) : (CAlg_R A) _⦋0⦌ :=
  cAlgVertexEquiv A ((cofibrantAlgebraDKCoprodWith A ((cAlgVertexEquiv A).symm y)).obj
    ((cAlgVertexEquiv A).symm x))

/-- 指定余積頂点は既存の coprodWith の値に厳密に一致する。 -/
lemma cAlgCoprodVertex_eq (x y : (CAlg_R A) _⦋0⦌) :
    cAlgCoprodVertex A x y = atVertex (barrattEcclesCoprodWith A y) x := by
  have h := cAlgCoprodWithModel_vertex A ((cAlgVertexEquiv A).symm y)
    ((cAlgVertexEquiv A).symm x)
  simpa [cAlgCoprodVertex, barrattEcclesCoprodWith] using h.symm

/-- 第一の厳密包含を表す辺。 -/
def cAlgCoprodInl (x y : (CAlg_R A) _⦋0⦌) :
    (CAlg_R A).Edge x (cAlgCoprodVertex A x y) :=
  (cAlgCofibrantArrow A (cofibrantAlgebraDKCoprodInl A
    ((cAlgVertexEquiv A).symm x) ((cAlgVertexEquiv A).symm y))).ofEq
      ((cAlgVertexEquiv A).apply_symm_apply x) rfl

/-- 第二の厳密包含を表す辺。 -/
def cAlgCoprodInr (x y : (CAlg_R A) _⦋0⦌) :
    (CAlg_R A).Edge y (cAlgCoprodVertex A x y) :=
  (cAlgCofibrantArrow A (cofibrantAlgebraDKCoprodInr A
    ((cAlgVertexEquiv A).symm x) ((cAlgVertexEquiv A).symm y))).ofEq
      ((cAlgVertexEquiv A).apply_symm_apply y) rfl

/-- 二つの厳密な包含を脚とする、指定二点図式の native な余錐。 -/
def cAlgCoprodCocone (x y : (CAlg_R A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram x y) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram x y) (z := cAlgCoprodVertex A x y)
    ((cAlgCoprodInl A x y).ofEq (by
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram, coprod.inl_desc]
      exact ((SSet.yonedaEquiv (X := CAlg_R A) (n := ⦋0⦌)).apply_symm_apply x).symm)
      rfl).toTruncated
    ((cAlgCoprodInr A x y).ofEq (by
      rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram, coprod.inr_desc]
      exact ((SSet.yonedaEquiv (X := CAlg_R A) (n := ⦋0⦌)).apply_symm_apply y).symm)
      rfl).toTruncated

/-- 作った余錐の頂点は、既存の余積関手の値である。 -/
lemma cAlgCoprodCocone_vertex (x y : (CAlg_R A) _⦋0⦌) :
    (cAlgCoprodCocone A x y).vertex = atVertex (barrattEcclesCoprodWith A y) x :=
  by
    unfold cAlgCoprodCocone
    rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges_vertex]
    exact cAlgCoprodVertex_eq A x y

/-- 作った余錐の第一脚は、指定した第一包含の同じ一次単体。 -/
lemma cAlgCoprodCocone_leg_left (x y : (CAlg_R A) _⦋0⦌) :
    ((cAlgCoprodCocone A x y).leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointLeft).edge = (cAlgCoprodInl A x y).edge :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges_leg_left _ _ _

/-- 作った余錐の第二脚は、指定した第二包含の同じ一次単体。 -/
lemma cAlgCoprodCocone_leg_right (x y : (CAlg_R A) _⦋0⦌) :
    ((cAlgCoprodCocone A x y).leg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointRight).edge = (cAlgCoprodInr A x y).edge :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryCoconeOfEdges_leg_right _ _ _

end SerrePositivity.EInfinity.BarrattEccles

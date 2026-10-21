module

public import SerrePositivity.InfinityCategories.Core.InnerAnodyneEquivalence
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.FunctorFiber
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn

/-!
概要：同じ接続する二辺を固定した、全合成三角形の空間は可縮。
方針：元の二辺を内ホーンへ貼り、内ホーン制限の自明 Kan fiber を取る。
規約：合成辺と三角形を選び直さず、全パラメーターで元の二辺を保持する。
使われ方：一次元の分類先の Hom fiber の、最初の合成三角形の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の二辺を、同じ接続頂点に沿って内ホーンへ厳密に貼る。 -/
def composableEdgeHorn {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) : (horn 2 1 : SSet.{u}) ⟶ X :=
  horn₂₁.isPushout.desc (SSet.yonedaEquiv.symm e.edge) (SSet.yonedaEquiv.symm f.edge) (by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact e.tgt_eq.trans f.src_eq.symm)

/-- 同じ内ホーンの第一辺は元の第一辺そのもの。 -/
lemma composableEdgeHorn_first {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) :
    horn₂₁.ι₀₁ ≫ composableEdgeHorn e f = SSet.yonedaEquiv.symm e.edge :=
  horn₂₁.isPushout.inl_desc _ _ _

/-- 同じ内ホーンの第二辺は元の第二辺そのもの。 -/
lemma composableEdgeHorn_last {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) :
    horn₂₁.ι₁₂ ≫ composableEdgeHorn e f = SSet.yonedaEquiv.symm f.edge :=
  horn₂₁.isPushout.inr_desc _ _ _

/-- 指定された同じ内ホーン上で固定した、全三角形の延長空間。 -/
def innerTriangleExtensionSpace {X : SSet.{u}} (a : (horn 2 1 : SSet.{u}) ⟶ X) : SSet.{u} :=
  vertexFiber ((pre (horn 2 1).ι).app X) (functorVertex a)

/-- 同じ指定内ホーンの三角形の延長空間は、可縮 Kan。 -/
lemma innerTriangleExtensionSpace_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (a : (horn 2 1 : SSet.{u}) ⟶ X) : IsContractibleKan (innerTriangleExtensionSpace a) := by
  letI : TrivialKanFibration ((pre (horn 2 1).ι).app X) :=
    trivialKanFibration_pre_of_innerAnodyne _
      (innerAnodyneExtensions.horn_ι (by decide) (by decide)) X
  exact vertexFiber_isContractibleKan _ _

/-- 指定された同じ二辺を固定した、全合成三角形の空間。 -/
def compositionTriangleSpace {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) : SSet.{u} :=
  innerTriangleExtensionSpace (composableEdgeHorn e f)

/-- 任意の quasicategory 内で、同じ指定二辺の全合成三角形の空間は可縮 Kan。 -/
lemma compositionTriangleSpace_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌} (e : X.Edge x y) (f : X.Edge y z) :
    IsContractibleKan (compositionTriangleSpace e f) :=
  innerTriangleExtensionSpace_isContractibleKan _

/-- 元の全合成三角形を、同じパラメーター全体で評価する普遍三角形。 -/
def compositionTriangleEvaluation {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) :
    (Δ[2] : SSet.{u}) ⊗ compositionTriangleSpace e f ⟶ X :=
  uncurry (vertexFiberι ((pre (horn 2 1).ι).app X) (functorVertex (composableEdgeHorn e f)))

/-- 同じ普遍三角形は、内ホーン上で元の二辺に全パラメーターで定値。 -/
lemma compositionTriangleEvaluation_horn {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) :
    ((horn 2 1).ι ▷ compositionTriangleSpace e f) ≫ compositionTriangleEvaluation e f =
      fst (horn 2 1 : SSet.{u}) (compositionTriangleSpace e f) ≫ composableEdgeHorn e f := by
  unfold compositionTriangleEvaluation
  rw [← uncurry_pre_app, vertexFiberι_comp, uncurry_const_functorVertex]

end SerrePositivity.InfinityCategories

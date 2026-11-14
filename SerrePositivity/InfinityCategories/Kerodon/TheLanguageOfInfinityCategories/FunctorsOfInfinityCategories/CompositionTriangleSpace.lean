module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.InnerAnodyneEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：同じ接続する二辺を固定した、全合成三角形の空間は可縮。
方針：元の二辺を内ホーンへ貼り、内ホーン制限の自明 Kan fiber を取る。
規約：合成辺と三角形を選び直さず、全パラメーターで元の二辺を保持する。
使われ方：一次元の分類先の Hom fiber の、最初の合成三角形の比較。

対応節は Kerodon 1.5（Tag 0055）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories

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
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)

/-- 同じ指定内ホーンの三角形の延長空間は、可縮 Kan。 -/
lemma innerTriangleExtensionSpace_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (a : (horn 2 1 : SSet.{u}) ⟶ X) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (innerTriangleExtensionSpace a) := by
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre (horn 2 1).ι).app X) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.trivialKanFibration_pre_of_innerAnodyne _
      (innerAnodyneExtensions.horn_ι (by decide) (by decide)) X
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan _ _

/-- 指定された同じ二辺を固定した、全合成三角形の空間。 -/
def compositionTriangleSpace {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) : SSet.{u} :=
  innerTriangleExtensionSpace (composableEdgeHorn e f)

/-- 任意の quasicategory 内で、同じ指定二辺の全合成三角形の空間は可縮 Kan。 -/
@[kerodon 007A]
lemma compositionTriangleSpace_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌} (e : X.Edge x y) (f : X.Edge y z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (compositionTriangleSpace e f) :=
  innerTriangleExtensionSpace_isContractibleKan _

/-- 元の全合成三角形を、同じパラメーター全体で評価する普遍三角形。 -/
def compositionTriangleEvaluation {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) :
    (Δ[2] : SSet.{u}) ⊗ compositionTriangleSpace e f ⟶ X :=
  uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (horn 2 1).ι).app X) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (composableEdgeHorn e f)))

/-- 同じ普遍三角形は、内ホーン上で元の二辺に全パラメーターで定値。 -/
lemma compositionTriangleEvaluation_horn {X : SSet.{u}} {x y z : X _⦋0⦌}
    (e : X.Edge x y) (f : X.Edge y z) :
    ((horn 2 1).ι ▷ compositionTriangleSpace e f) ≫ compositionTriangleEvaluation e f =
      fst (horn 2 1 : SSet.{u}) (compositionTriangleSpace e f) ≫ composableEdgeHorn e f := by
  unfold compositionTriangleEvaluation
  rw [← uncurry_pre_app, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.3.2.3"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.compositionTriangleSpace_isContractibleKan

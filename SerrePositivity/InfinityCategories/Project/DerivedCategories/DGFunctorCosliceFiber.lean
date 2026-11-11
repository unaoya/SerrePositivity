module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedCosliceFiber
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorCoslicePostcomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorPinchedMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiberTransportSquare
/-!
概要：同じ dg 関手の実 coslice 後合成が誘導する、標準端点での実 fiber 射を計算する。
方針：底の頂点表示を等式でそろえ、包含と全単体座標を同時に保存する。
規約：任意の dg 関手。使われ方：Hom 単位前合成と関手像の合成比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
/-- 底の頂点等式による fiber 輸送は、元の同じ全空間の単体を保つ。 -/
lemma dgVertexFiberEqTransport_val {E B : SSet.{w}} (p : E ⟶ B) {a b : B _⦋0⦌}
    (h : a = b) {n : ℕ} (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p a) _⦋n⦌) :
    ((eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h)).app _ t).val = t.val := by
  subst b
  rfl
/-- 同じ頂点等式による fiber 輸送は、元の全空間への包含を保つ。 -/
lemma dgVertexFiberEqTransport_ι {E B : SSet.{w}} (p : E ⟶ B) {a b : B _⦋0⦌}
    (h : a = b) : eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p) h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p a := by
  subst b
  simp only [eqToHom_refl, Category.id_comp]
variable (R : Type u) [CommRing R] {D E : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
  (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) (x y : D)
/-- 同じ dg 関手の実 coslice 写像の fiber 射を標準終点へ正規化する。 -/
def dgFunctorCosliceFiber :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap _ _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCoslicePostcomp R F x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCoslicePostcomp_projection R F x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ≫
      eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
        ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)))))
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y))
/-- 同じ実 fiber 射は、元の実 coslice 全体への包含と可換。 -/
lemma dgFunctorCosliceFiber_ι :
    dgFunctorCosliceFiber R F x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCoslicePostcomp R F x := by
  rw [dgFunctorCosliceFiber, Category.assoc,
    dgVertexFiberEqTransport_ι _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y), _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap_ι]
/-- 同じ実 fiber 射の全単体座標は、元の同じ dg 関手像。 -/
lemma dgFunctorCosliceFiber_simplex {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex n ((dgFunctorCosliceFiber R F x y).app _ t) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex n t).map F := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftPointStdSimplexIso n).inv ≫
    ((eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
      ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)))))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y))).app _ _).val.val) = _
  rw [dgVertexFiberEqTransport_val _ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex F y)]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPointCosliceSimplex _
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCoslicePostcomp R F x).app _ t.val)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorCoslicePostcomp_coordinate, SSet.yonedaEquiv_comp]
  rfl
/-- 同じ実 fiber 射を標準左 Hom の同型で移したもの。 -/
def dgFunctorCosliceLeftMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).hom ≫
    dgFunctorCosliceFiber R F x y ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y))).inv
/-- 同じ左 Hom の写像も、元の同じ全単体の dg 関手像を保つ。 -/
lemma dgFunctorCosliceLeftMap_simplex {n : ℕ}
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n ((dgFunctorCosliceLeftMap R F x y).app _ t) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftSimplexVal n t).map F := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) (F.obj x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y))
  have hm : e.hom.app _ ((dgFunctorCosliceLeftMap R F x y).app _ t) =
      (dgFunctorCosliceFiber R F x y).app _
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedLeftCosliceFiberIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)).hom.app _ t) := by
    change e.hom.app _ (e.inv.app _ _) = _
    exact ConcreteCategory.congr_hom (NatTrans.congr_app e.inv_hom_id _) _
  calc
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberSimplex n (e.hom.app _ _) :=
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedCosliceFiberIso_simplex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R E)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj x)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (F.obj y)) _).symm
    _ = _ := by rw [hm, dgFunctorCosliceFiber_simplex, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgLeftPinchedCosliceFiberIso_simplex]
end SerrePositivity.InfinityCategories.Project.DerivedCategories

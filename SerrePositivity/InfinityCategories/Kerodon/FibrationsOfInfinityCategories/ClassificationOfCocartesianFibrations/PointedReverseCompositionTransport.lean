module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PointedSpaceParametrizedEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.DiagonalFiberTransportSquare

/-!
概要：反対 Kan 圏の豊穣合成を実際の pointed-space 射影の輸送族へ移す。
方針：底の同型を coslice 全体へ持ち上げ、同じ合成 prism の両端を正規化する。
規約：一点 Hom と辺のパラメーターの反転を保持し、fiber の逆同値を選ばない。
使われ方：pointed 自然性の二段輸送と Kan 値の Hom の作用を接続する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

local instance : ∀ A B : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}ᵒᵖ, KanComplex (SimplicialCategory.sHom A B) :=
  fun A B ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom B.unop A.unop))

/-- 反対 Kan nerve の一点 coslice と実際の pointed-space 全空間の同型。 -/
def reverseKanPointCosliceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm
      (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.{u})))) ≅
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCoslicePostIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso
    (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject))) ≪≫
  eqToIso (congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm z))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso_vertex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject))

/-- 一点 coslice の全空間の同型は元の底の同型を厳密に被覆する。 -/
lemma reverseKanPointCosliceIso_projection :
    reverseKanPointCosliceIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm
        (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.{u})))) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso.hom := by
  change reverseKanPointCosliceIso.hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject)) = _
  dsimp only [reverseKanPointCosliceIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnder_eqToHom_projection
    (congrArg SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso_vertex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject))]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCoslicePostIso_projection _ _

/-- 反転した一点 Hom を、空間 K 上の実際の pointed fiber へ写す比較。 -/
def pointedReverseKanFiberComparison (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (Opposite.op K) (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject))).op ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseSliceFiberComparison (Opposite.op K) (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ reverseKanPointCosliceIso.hom) (by
        rw [Category.assoc, Category.assoc, reverseKanPointCosliceIso_projection,
          ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _) _ _, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.const_comp,
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso_vertex, SSet.comp_const])

/-- 元の反転した豊穣 Hom の区間族を SpaceInfinity へ移した同じ底の族。 -/
def pointedReverseKanHomInterval (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    Δ[1] ⊗ ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (Opposite.op L) (Opposite.op K))).op ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseHomInterval (Opposite.op L) (Opposite.op K) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso.hom

/-- 移した区間族の始点は元の Kan 空間 K。 -/
lemma pointedReverseKanHomInterval_zero (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 _ ≫ pointedReverseKanHomInterval K L =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K) := by
  rw [pointedReverseKanHomInterval, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.coherentReverseHomInterval_zero,
    SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso_vertex]

/-- 移した区間族の終点は元の Kan 空間 L。 -/
lemma pointedReverseKanHomInterval_one (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 _ ≫ pointedReverseKanHomInterval K L =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex L) := by
  rw [pointedReverseKanHomInterval, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.coherentReverseHomInterval_one,
    SSet.const_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso_vertex]

/-- 全ての一点 Hom と豊穣射に対する実際の pointed-space の合成輸送族。 -/
def pointedReverseKanCompositionTransportFamily (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex L) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (pointedReverseKanFiberComparison K) (pointedReverseKanHomInterval K L) where
  endpoint := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
    (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject) ≫ pointedReverseKanFiberComparison L
  prism := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionReversePrism (Opposite.op L) (Opposite.op K)
    (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject) ≫ reverseKanPointCosliceIso.hom
  start := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionReversePrism_zero]
    rfl
  finish := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionReversePrism_one]
    rfl
  over_base := by
    rw [Category.assoc, reverseKanPointCosliceIso_projection, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionReversePrism_projection, Category.assoc]
    rfl

/-- 同じ反転した一点 Hom の作用は、実際の pointed-space の普遍輸送と関手同型。 -/
def pointedReverseKanCompositionTransport_parametrizedIso (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
        (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject) ≫ pointedReverseKanFiberComparison L))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (pointedReverseKanHomInterval K L)
        (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex K) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex L) ≫
      (pre (pointedReverseKanFiberComparison K)).app
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex L))) :=
  (pointedReverseKanCompositionTransportFamily K L).mapIso_parametrizedSource
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection _ _
    (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L)

/-- 動く一点 Hom と辺への同時評価でも、同じ豊穣合成が実際の対角輸送を与える。 -/
def pointedReverseKanCompositionTransport_diagonalIso
    {P : SSet.{u + 1}} (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
    (x : P ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (Opposite.op K) (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject))).op)
    (y : P ⟶ ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (Opposite.op L) (Opposite.op K))).op) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (lift x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
        (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject) ≫ pointedReverseKanFiberComparison L)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.diagonalFiberTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (x ≫ pointedReverseKanFiberComparison K)
        (y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (pointedReverseKanHomInterval K L)
          (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L))) :=
  (pointedReverseKanCompositionTransportFamily K L).diagonalIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection _ _
    (pointedReverseKanHomInterval_zero K L) (pointedReverseKanHomInterval_one K L) x y

/-- 実際の pointed fiber への反転した一点 Hom 比較は同値。 -/
lemma pointedReverseKanFiberComparison_isQCatEquivalence (K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (pointedReverseKanFiberComparison K) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm
    (SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.{u}))))
  let a := SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (Opposite.op K))
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap p _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection reverseKanPointCosliceIso.hom
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso.hom reverseKanPointCosliceIso_projection a
  have : IsIso k := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSquareFiberMap_isIso p _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
    reverseKanPointCosliceIso _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso reverseKanPointCosliceIso_projection a
  let e := asIso k ≪≫ eqToIso
    (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.reverseKanNerveSpaceIso_vertex K))
  have he : pointedReverseKanFiberComparison K =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseSliceFiberComparison (Opposite.op K) (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject) ≫
        e.hom := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl
  rw [he]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.coherentReverseSliceFiberComparison_homotopyEquivalence
    (Opposite.op K) (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject)).isQCatEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

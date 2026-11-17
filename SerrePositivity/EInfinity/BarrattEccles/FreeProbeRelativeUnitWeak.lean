module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeUnitReference
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementWeak
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.UnitComparisonWeakDetection
/-!
概要：元の自由単位による実 U の局所化源頂点での Hom 比較を検査する。
方針：同じ弱な全要素族と弱な複体屋根族を元の単位三角形で接続する。
規約：元の単位成分・実 U・全パラメータ・実端点同型を保持する。
使われ方：標準導来単位比較への頂点輸送の前段。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.InfinityCategories SerrePositivity.DifferentialGraded
open SerrePositivity.EInfinity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：元の単位成分を実 U の同じ自由局所化源頂点へ送る。
方針：同じ通常単位の導来像と全源同型の評価の逆を合成する。
規約：元の単位を保持。使われ方：同じ局所化源での実単位誘導射。 -/
def freeProbeRelativeUnitHom :
    (HomotopyCategory.mk ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((ComplexLimits.framedLimitProbeFunctor A).obj X))) :
        hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)) ⟶
    HomotopyCategory.mk ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
      ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (freeProbeRelativeElementSource A X)))) :=
  freeProbeUnitOrdinaryHom A X ≫
    (cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X)).inv

/-- 概要：同じ局所化源頂点での実 U と元の自由単位による区間 Hom 比較。
方針：同じ忘却作用の後で元の単位成分を前合成する。
規約：実際の比較射を定義。使われ方：標準単位比較への弱同値性の輸送。 -/
def freeProbeRelativeUnitIntervalMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (freeProbeRelativeElementSource A X)))
      ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B))) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
      ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex ((ComplexLimits.framedLimitProbeFunctor A).obj X)))
      ((cAlgForgetDerived A).app (Opposite.op ⦋0⦌)
        ((cAlgLocalizationSource A).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (cAlgForgetDerived A) _ _ ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose _ (freeProbeRelativeUnitHom A X)

/-- 概要：元の単位の全屋根三角形は同じ相対パラメータでも成立する。
方針：元の全三角形を同じ down で前合成する。
規約：全射と同じパラメータを保持。使われ方：元の実単位比較の全族判定。 -/
lemma freeProbeRelativeUnderlyingRoofFamily_unit_triangle :
    let K := nerve (freeProbeRelativeElementIndex A X B)
    let d := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj)
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (freeProbeUnitOrdinaryHom A X) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp d (freeProbeElementUnderlyingRoofFamily A X B.obj) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp d
      (normalizedTensorElementDerivedRoofFamily A ((ComplexLimits.framedLimitProbeFunctor A).obj X)
        (complexSemifreeResolutionValue A B.obj.carrier).val) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk (complexSemifreeResolutionValueAugmentation A B.obj.carrier)).map
          (complexOrdinaryDerivedSource A)).toTruncated) := by
  let d := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj)
  let T := (hoFunctor.map ((pre d).app (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A))).toFunctor
  have h := congrArg T.map (freeProbeElementUnderlyingRoofFamily_unit_triangle A X B.obj)
  simp only [Functor.map_comp] at h
  have hu := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_precomp (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) d
    (freeProbeUnitOrdinaryHom A X)
  have ha := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_precomp (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) d
    (Truncated.HomotopyCategory.homMk
    ((nerve.edgeMk (complexSemifreeResolutionValueAugmentation A B.obj.carrier)).map
      (complexOrdinaryDerivedSource A)).toTruncated)
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHomPrecomp] at hu ha ⊢
  rw [hu, ha] at h
  exact h

/-- 概要：同じ弱な全要素族上で元の実単位比較は複体屋根基準族と一致する。
方針：実 U の全忘却屋根公式と元の単位三角形を接続する。
規約：全 h Fun の射の等式。使われ方：元の単位誘導射自身の弱同値性。 -/
lemma freeProbeRelativeUnitIntervalMap_family :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom ((freeProbeRelativeElementPinchedMap A X B ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) ≫ freeProbeRelativeUnitIntervalMap A X B) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (freeProbeRelativeUnitReference A X B ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  let K := nerve (freeProbeRelativeElementIndex A X B)
  let d := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.down (freeProbeElementIndex A X B.obj)
  let e := cofibrantForgetOrdinaryVertexIso A (freeProbeElementCofibrantSource A X)
  have hf := (Arrow.mk_injective _ _) (freeProbeRelativeElementPinched_forget_family_arrow A X B)
  rw [freeProbeRelativeUnitIntervalMap, Category.assoc, ← Category.assoc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap (cAlgForgetDerived A) _ _),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pinchedHomToIntervalMappingSpace_naturality]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_family, hf,
    freeProbeRelativeUnitHom, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K e.inv) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K e.hom),
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp, e.inv_hom_id, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_id, Category.id_comp]
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (freeProbeUnitOrdinaryHom A X)),
    freeProbeRelativeUnderlyingRoofFamily_unit_triangle]
  rw [freeProbeRelativeUnitReference_family, freeProbeRelativeTargetHom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_comp]
  simp only [Category.assoc]

/-- 概要：同じ局所化源での元の単位 Hom 比較自身は弱同値。
方針：弱な全 CAlg_R 族上の全族等式から弱な複体基準射で反映する。
規約：元の実比較射を結論に残す。使われ方：標準導来単位比較への端点輸送。 -/
lemma freeProbeRelativeUnitIntervalMap_weak :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (freeProbeRelativeUnitIntervalMap A X B) := by
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.unitComparison_weak_of_probe_family (freeProbeRelativeUnitIntervalMap A X B)
    (freeProbeRelativeElementPinchedMap A X B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)
    (freeProbeRelativeUnitReference A X B)
    ((freeProbeRelativeElementPinchedMap_weak A X B).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence _ _).isWeakHomotopyEquivalence)
    (freeProbeRelativeUnitReference_weak A X B)
    (freeProbeRelativeUnitIntervalMap_family A X B)

end SerrePositivity.EInfinity.BarrattEccles

module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementPinched
public import SerrePositivity.EInfinity.BarrattEccles.CAlgForgetDerived
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixFamilyTriangle
public import SerrePositivity.EInfinity.ComplexLimits.PinchedFamilyPostcompArrow
/-! 概要：元の自由列の CAlg_R 全 pinched 族を同じ実屋根へ比較する。
方針：元の全 slice 三角形と後合成の Arrow 等式を使う。
規約：全パラメータ・同じ augmentation の逆・評価を保持する。
使われ方：実 U と標準導来単位比較の全族三角形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet MonoidalClosed Hammock _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：元の自由列の実 Kan hammock pinched 全族。
方針：同じ roof と Ex∞ 単位に元の Hom 比較を合成する。
規約：実局所化源の両端点を保持。使われ方：全族の後合成比較。 -/
def freeProbeRelativeElementHammockPinchedMap : nerve (freeProbeRelativeElementIndex A X B) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)).app (op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (freeProbeRelativeElementSource A X)))
      ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)).app (op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B))) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.familyMap (cofibrantAlgebraRelativeCategory A)
    (freeProbeRelativeElementColumn A X B) (freeProbeRelativeElementAugmentation A X B)
    (freeProbeRelativeElementAugmentation_weak A X B) (freeProbeRelativeElementEvaluation A X B)
    (fun f => freeProbeRelativeElementColumn_map_weak A X B f) ≫
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockHomPinchedMap (cofibrantAlgebraRelativeCategory A)
        (freeProbeRelativeElementSource A X) (ULiftHom.objUp.{u + 1, u + 1} B)

/-- 概要：CAlg_R の元の全 pinched 族は同じ実局所化同値による像。
方針：元の全写像の合成を展開する。規約：全要素を保持。
使われ方：実 U の後合成との接続。 -/
lemma freeProbeRelativeElementPinchedMap_eq_hammock : freeProbeRelativeElementPinchedMap A X B =
    freeProbeRelativeElementHammockPinchedMap A X B ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationEquivalence (cofibrantAlgebraRelativeCategory A)).hom
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)).app (op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (freeProbeRelativeElementSource A X)))
        ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.hammockLocalizationNerveMap (cofibrantAlgebraRelativeCategory A)).app (op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} B))) := by
  simp only [freeProbeRelativeElementPinchedMap, freeProbeRelativeElementHammockPinchedMap,
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.familyMap, freeProbeRelativeElementRoofMap, freeProbeRelativeElementRoof,
    Category.assoc]

/-- 概要：任意の後合成後も元の全族は同じ実屋根を表す。
方針：全評価三角形と同じ pinched 後合成の Arrow 等式を接続する。
規約：全族・両端表示・指定 augmentation の逆を保持。
使われ方：実 U の全族と元の複体屋根の照合。 -/
lemma freeProbeRelativeElementHammockFamily_postcomp_arrow {D : SSet.{u + 1}}
    (F : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockNerve (cofibrantAlgebraRelativeCategory A) ⟶ D) :
    let C := cofibrantAlgebraRelativeCategory A
    let U := freeProbeRelativeElementColumn A X B
    let p := freeProbeRelativeElementAugmentation A X B
    let hp := freeProbeRelativeElementAugmentation_weak A X B
    let σ := freeProbeRelativeElementEvaluation A X B
    let T := (hoFunctor.map ((ihom (nerve (freeProbeRelativeElementIndex A X B))).map F)).toFunctor
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (freeProbeRelativeElementHammockPinchedMap A X B ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk (T.map ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.coherentAugmentationIso C U p hp).inv ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.coherentAugmentationHomotopy C U σ)))) := by
  dsimp only
  refine (ComplexLimits.pinchedFamilyPostcomp_arrow F
    (freeProbeRelativeElementHammockPinchedMap A X B)).trans ?_
  let T := (hoFunctor.map
    ((ihom (nerve (freeProbeRelativeElementIndex A X B))).map F)).toFunctor
  exact congrArg T.mapArrow.obj
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.native_family_eq_roof_arrow (cofibrantAlgebraRelativeCategory A)
      (freeProbeRelativeElementColumn A X B) (freeProbeRelativeElementAugmentation A X B)
      (freeProbeRelativeElementAugmentation_weak A X B)
      (freeProbeRelativeElementEvaluation A X B)
      (fun f => freeProbeRelativeElementColumn_map_weak A X B f))

/-- 概要：同じ実 U による CAlg_R 全 pinched 族の像は元の屋根の像。
方針：同じ局所化同値と実 U の合成を全族の後合成公式へ代入する。
規約：U・元の全 K・元の指定左脚を保持。使われ方：標準単位の弱同値判定。 -/
lemma freeProbeRelativeElementPinched_forget_arrow :
    let C := cofibrantAlgebraRelativeCategory A
    let U := freeProbeRelativeElementColumn A X B
    let p := freeProbeRelativeElementAugmentation A X B
    let hp := freeProbeRelativeElementAugmentation_weak A X B
    let σ := freeProbeRelativeElementEvaluation A X B
    let F := (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationEquivalence C).hom ≫ cAlgForgetDerived A
    let T := (hoFunctor.map ((ihom (nerve (freeProbeRelativeElementIndex A X B))).map F)).toFunctor
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (freeProbeRelativeElementPinchedMap A X B ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (cAlgForgetDerived A) _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk (T.map ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.coherentAugmentationIso C U p hp).inv ≫
      SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.coherentAugmentationHomotopy C U σ)))) := by
  dsimp only
  rw [freeProbeRelativeElementPinchedMap_eq_hammock]
  simp only [Category.assoc]
  exact freeProbeRelativeElementHammockFamily_postcomp_arrow A X B
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationEquivalence (cofibrantAlgebraRelativeCategory A)).hom ≫
      cAlgForgetDerived A)

end SerrePositivity.EInfinity.BarrattEccles

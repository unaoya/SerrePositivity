module
public import SerrePositivity.EInfinity.BarrattEccles.FreeProbeRelativeElementFamilyComparison
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumnRoofNaturality
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixColumnRoof
/-! 概要：元の自由列の全屋根を実 U の全局所化源比較で移す。
方針：同じ U の全源同型と元の augmentation・評価を全屋根自然性へ代入する。
規約：同じ全要素圏と元の両端を保持する。
使われ方：実 pinched 全族と元の複体単位三角形の接合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : Complex A) (B : CofibrantAlgebra A)

/-- 概要：元の自由列の左脚は実 U の局所化源で反転される。
方針：同じ指定弱同値と実 U による後合成を使う。
規約：実 U 自身を保持。使われ方：元の全屋根の反転。 -/
lemma freeProbeRelativeElementAugmentation_forget_invertible
    (s : freeProbeRelativeElementIndex A X B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk ((freeProbeRelativeElementAugmentation A X B).app s)).map
      (cAlgLocalizationSource A ≫ cAlgForgetDerived A)).toTruncated :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.weakNerveEdges_inverts_arrows (cofibrantAlgebraRelativeCategory A) _
    ((cAlgLocalizationSource_inverts A).comp (cAlgForgetDerived A)) _
    (freeProbeRelativeElementAugmentation_weak A X B s)

/-- 概要：元の自由列の左脚は同じ通常忘却の導来源で反転される。
方針：同じ弱同値の忘却の準同型を使う。
規約：元の全射を保持。使われ方：全源比較の右側の屋根。 -/
lemma freeProbeRelativeElementAugmentation_underlying_invertible
    (s : freeProbeRelativeElementIndex A X B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge ((nerve.edgeMk ((freeProbeRelativeElementAugmentation A X B).app s)).map
      (cofibrantAlgebraUnderlyingDerivedSource A)).toTruncated :=
  cofibrantAlgebraUnderlyingDerivedSource_map_weak A _
    (freeProbeRelativeElementAugmentation_weak A X B s)

/-- 概要：同じ実 U の全源同型は元の全自由屋根と可換。
方針：元の左右脚を全屋根自然性へ代入する。
規約：元の全パラメータと指定 U を保持。使われ方：単位の全族三角形の接合。 -/
lemma freeProbeRelativeElementRoof_source_naturality :
    let V := freeProbeRelativeElementColumn A X B
    let p := freeProbeRelativeElementAugmentation A X B
    let σ := freeProbeRelativeElementEvaluation A X B
    let K := freeProbeRelativeElementIndex A X B
    let F := cAlgLocalizationSource A ≫ cAlgForgetDerived A
    let G := cofibrantAlgebraUnderlyingDerivedSource A
    ((cAlgForgetDerived_sourceIso A).precomp
      (nerveMap ((Functor.const K).obj (freeProbeRelativeElementSource A X)))).hom ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso G V p
        (freeProbeRelativeElementAugmentation_underlying_invertible A X B)).inv ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom G σ =
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso F V p
      (freeProbeRelativeElementAugmentation_forget_invertible A X B)).inv ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F σ ≫
      ((cAlgForgetDerived_sourceIso A).precomp
        (nerveMap ((Functor.const K).obj (ULiftHom.objUp.{u + 1, u + 1} B)))).hom :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.roof_naturality (cAlgForgetDerived_sourceIso A)
    (freeProbeRelativeElementColumn A X B) (freeProbeRelativeElementAugmentation A X B)
    (freeProbeRelativeElementAugmentation_forget_invertible A X B)
    (freeProbeRelativeElementAugmentation_underlying_invertible A X B)
    (freeProbeRelativeElementEvaluation A X B)

/-- 概要：実 U による元の全 pinched 族は全局所化源の同じ屋根を表す。
方針：元の全 slice 三角形の後合成を同じ通常列へ回収する。
規約：実 U と同じ全パラメータを保持。使われ方：全源比較への入口。 -/
lemma freeProbeRelativeElementPinched_forget_column_roof_arrow :
    let V := freeProbeRelativeElementColumn A X B
    let p := freeProbeRelativeElementAugmentation A X B
    let σ := freeProbeRelativeElementEvaluation A X B
    let F := cAlgLocalizationSource A ≫ cAlgForgetDerived A
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (freeProbeRelativeElementPinchedMap A X B ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (cAlgForgetDerived A) _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso F V p
      (freeProbeRelativeElementAugmentation_forget_invertible A X B)).inv ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F σ) := by
  dsimp only
  rw [freeProbeRelativeElementPinchedMap_eq_hammock]
  simp only [Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.native_family_postcomp_column_roof_arrow
    (cofibrantAlgebraRelativeCategory A) (freeProbeRelativeElementColumn A X B)
    (freeProbeRelativeElementAugmentation A X B)
    (freeProbeRelativeElementAugmentation_weak A X B)
    (freeProbeRelativeElementEvaluation A X B)
    (fun f => freeProbeRelativeElementColumn_map_weak A X B f)
    ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.kanHammockLocalizationEquivalence (cofibrantAlgebraRelativeCategory A)).hom ≫
      cAlgForgetDerived A)

/-- 概要：実 U の全局所化源の屋根は元の忘却屋根の同じ全共役。
方針：元の全源自然性の右端同型を反転する。
規約：全端点同型と元の左右脚を保持。使われ方：元の単位三角形の輸送。 -/
lemma freeProbeRelativeElementSourceRoof_eq_underlying :
    let V := freeProbeRelativeElementColumn A X B
    let p := freeProbeRelativeElementAugmentation A X B
    let σ := freeProbeRelativeElementEvaluation A X B
    let K := freeProbeRelativeElementIndex A X B
    let F := cAlgLocalizationSource A ≫ cAlgForgetDerived A
    let G := cofibrantAlgebraUnderlyingDerivedSource A
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso F V p
      (freeProbeRelativeElementAugmentation_forget_invertible A X B)).inv ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F σ =
    ((cAlgForgetDerived_sourceIso A).precomp
      (nerveMap ((Functor.const K).obj (freeProbeRelativeElementSource A X)))).hom ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso G V p
        (freeProbeRelativeElementAugmentation_underlying_invertible A X B)).inv ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom G σ ≫
      ((cAlgForgetDerived_sourceIso A).precomp
        (nerveMap ((Functor.const K).obj (ULiftHom.objUp.{u + 1, u + 1} B)))).inv := by
  have h := freeProbeRelativeElementRoof_source_naturality A X B
  have h' := congrArg (fun z => z ≫ ((cAlgForgetDerived_sourceIso A).precomp
    (nerveMap ((Functor.const (freeProbeRelativeElementIndex A X B)).obj
      (ULiftHom.objUp.{u + 1, u + 1} B)))).inv) h.symm
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h'

/-- 概要：元の実 pinched 全族の U 像は同じ忘却屋根の全端点輸送。
方針：元の全 slice 三角形を同じ全源自然性へ接続する。
規約：実 U・全 K・元の端点同型を保持。使われ方：元の単位の全族三角形。 -/
lemma freeProbeRelativeElementPinched_forget_underlying_arrow :
    let V := freeProbeRelativeElementColumn A X B
    let p := freeProbeRelativeElementAugmentation A X B
    let σ := freeProbeRelativeElementEvaluation A X B
    let K := freeProbeRelativeElementIndex A X B
    let G := cofibrantAlgebraUnderlyingDerivedSource A
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (freeProbeRelativeElementPinchedMap A X B ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap (cAlgForgetDerived A) _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
    Arrow.mk (((cAlgForgetDerived_sourceIso A).precomp
      (nerveMap ((Functor.const K).obj (freeProbeRelativeElementSource A X)))).hom ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso G V p
        (freeProbeRelativeElementAugmentation_underlying_invertible A X B)).inv ≫
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom G σ ≫
      ((cAlgForgetDerived_sourceIso A).precomp
        (nerveMap ((Functor.const K).obj (ULiftHom.objUp.{u + 1, u + 1} B)))).inv) :=
  (freeProbeRelativeElementPinched_forget_column_roof_arrow A X B).trans
    (congrArg Arrow.mk (freeProbeRelativeElementSourceRoof_eq_underlying A X B))

end SerrePositivity.EInfinity.BarrattEccles

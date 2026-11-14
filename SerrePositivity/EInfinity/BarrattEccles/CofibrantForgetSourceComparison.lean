module
public import SerrePositivity.EInfinity.BarrattEccles.CofibrantUnderlyingConstantRestriction
public import SerrePositivity.EInfinity.FrameHom.NerveColumnNaturalityComponent
/-!
概要：実 U の全源比較と元の cofibrant 通常射の指定正方形を回収する。
方針：閉包内の全列自然性を同じ射の定値列に適用し、同じ成分辺を評価する。
規約：全源同型・元の射・元の通常忘却を保持する。
使われ方：元の置換 augmentation に沿う標準単位の端点整合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet SerrePositivity.InfinityCategories
open SerrePositivity.EInfinity.FrameHom
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 概要：実 U の全源同型は元の cofibrant 通常射の両像と可換。
方針：既存の全列自然性の指定成分を評価する。
規約：同じ実射を保持。使われ方：置換 augmentation の源比較正方形。 -/
lemma cofibrantForgetSource_component_square
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y) :
    Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk f).map (cAlgLocalizationSource A ≫ cAlgForgetDerived A)).toTruncated ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (cAlgForgetDerived_sourceIso A).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex Y) =
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (cAlgForgetDerived_sourceIso A).hom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X) ≫
      Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk f).map (cofibrantAlgebraUnderlyingDerivedSource A)).toTruncated := by
  exact (Arrow.mk_injective _ _)
    (NerveColumn.hom_naturality_const_component (cAlgForgetDerived_sourceIso A) f)

/-- 概要：元の通常忘却による成分辺の導来像は同じ通常複体射の導来像。
方針：元の零単体表示と同じ一次単体の計算で辺の類を輸送する。
規約：元の成分辺を保持。使われ方：全源自然性の通常複体端点への回収。 -/
lemma cofibrantUnderlying_component_transport (X Y : CofibrantAlgebra A)
    (f : ULiftHom.objUp.{u + 1, u + 1} X ⟶ ULiftHom.objUp.{u + 1, u + 1} Y) :
    (eqToIso (congrArg HomotopyCategory.mk (cofibrantUnderlying_ordinary_vertex A X))).inv ≫
      Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk f).map (cofibrantAlgebraUnderlyingDerivedSource A)).toTruncated ≫
      (eqToIso (congrArg HomotopyCategory.mk (cofibrantUnderlying_ordinary_vertex A Y))).hom =
    Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk ((cofibrantAlgebraDKForget A).map f)).map
        (ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated := by
  have he := congrArg ((ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌))
    (cofibrantAlgebraForgetNerve_mk₁ A f)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (X := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A)
    (cofibrantUnderlying_ordinary_vertex A X) (cofibrantUnderlying_ordinary_vertex A Y)
    ((nerve.edgeMk f).map (cofibrantAlgebraUnderlyingDerivedSource A)).toTruncated
    ((nerve.edgeMk ((cofibrantAlgebraDKForget A).map f)).map
      (ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated he

/-- 概要：元の cofibrant 射の実 U 像は同じ通常複体の頂点比較と可換。
方針：同じ全源正方形を元の通常忘却の端点輸送へ接続する。
規約：実 U と同じ指定射を保持。使われ方：標準単位の置換端点の照合。 -/
lemma cofibrantForgetOrdinary_component_square (X Y : CofibrantAlgebra A)
    (f : ULiftHom.objUp.{u + 1, u + 1} X ⟶ ULiftHom.objUp.{u + 1, u + 1} Y) :
    (hoFunctor.map (cAlgForgetDerived A)).toFunctor.map
        (Truncated.HomotopyCategory.homMk
          ((nerve.edgeMk f).map (cAlgLocalizationSource A)).toTruncated) ≫
      (cofibrantForgetOrdinaryVertexIso A Y).hom =
    (cofibrantForgetOrdinaryVertexIso A X).hom ≫ Truncated.HomotopyCategory.homMk
      ((nerve.edgeMk ((cofibrantAlgebraDKForget A).map f)).map
        (ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated := by
  let ex := eqToIso (congrArg HomotopyCategory.mk (cofibrantUnderlying_ordinary_vertex A X))
  let ey := eqToIso (congrArg HomotopyCategory.mk (cofibrantUnderlying_ordinary_vertex A Y))
  let g := Truncated.HomotopyCategory.homMk
    ((nerve.edgeMk f).map (cofibrantAlgebraUnderlyingDerivedSource A)).toTruncated
  let h := Truncated.HomotopyCategory.homMk
    ((nerve.edgeMk ((cofibrantAlgebraDKForget A).map f)).map
      (ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated
  have ht : ex.inv ≫ g ≫ ey.hom = h := cofibrantUnderlying_component_transport A X Y f
  have ht' : g ≫ ey.hom = ex.hom ≫ h := by
    rw [← ht]
    simp only [Iso.hom_inv_id_assoc]
  have hf : (hoFunctor.map (cAlgForgetDerived A)).toFunctor.map
      (Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk f).map (cAlgLocalizationSource A)).toTruncated) =
      Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk f).map (cAlgLocalizationSource A ≫ cAlgForgetDerived A)).toTruncated := by
    change (Truncated.mapHomotopyCategory ((truncation 2).map (cAlgForgetDerived A))).map _ = _
    rw [Truncated.mapHomotopyCategory_homMk]
    rfl
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (cAlgForgetDerived_sourceIso A).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} Y)) ≫
      ey.hom) =
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (cAlgForgetDerived_sourceIso A).hom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (ULiftHom.objUp.{u + 1, u + 1} X)) ≫ ex.hom) ≫ h
  have hn := cofibrantForgetSource_component_square A f
  rw [hf, ← Category.assoc, hn, Category.assoc, ht']
  simp only [Category.assoc]

/-- 概要：元の置換 augmentation の U 像は同じ通常 augmentation の導来像。
方針：元の cofibrant 置換成分を通常忘却の正方形へ代入する。
規約：任意の cofibrant 代数を保つ。使われ方：自由 probe への反転成分の特殊化。 -/
lemma cofibrantReplacement_forget_ordinary_arrow (B : CofibrantAlgebra A) :
    Arrow.mk ((hoFunctor.map (cAlgForgetDerived A)).toFunctor.map
      (Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk ((cofibrantDKComparison A).app
          (ULiftHom.objUp.{u + 1, u + 1} B))).map (cAlgLocalizationSource A)).toTruncated) ≫
        (cofibrantForgetOrdinaryVertexIso A B).hom) =
    Arrow.mk ((cofibrantForgetOrdinaryVertexIso A
        ((cofibrantAlgebraReplacement A).obj B.obj)).hom ≫
      Truncated.HomotopyCategory.homMk
        ((nerve.edgeMk (framedLimitProbeComparison A B.obj).hom).map
          (ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated) := by
  let R := (cofibrantAlgebraReplacement A).obj B.obj
  let f : ULiftHom.objUp.{u + 1, u + 1} R ⟶ ULiftHom.objUp.{u + 1, u + 1} B :=
    (cofibrantDKComparison A).app (ULiftHom.objUp.{u + 1, u + 1} B)
  have hn := cofibrantForgetOrdinary_component_square A R B f
  have hf : (cofibrantAlgebraDKForget A).map f = (framedLimitProbeComparison A B.obj).hom := rfl
  rw [hf] at hn
  exact congrArg Arrow.mk hn

end SerrePositivity.EInfinity.BarrattEccles

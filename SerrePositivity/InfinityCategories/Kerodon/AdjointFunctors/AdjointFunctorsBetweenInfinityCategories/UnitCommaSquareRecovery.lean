module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.CommaSquareUncurry
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCompositionTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaArrowFamilies
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaComparisonHomotopy

/-!
概要：単位比較の像から指定終辺へのホモトピーから comma の正方形と写像空間の族を復元する。
方針：合成三角形を運び、退化三角形で正方形へ補完して uncurry する。
規約：指定した単位・終辺・Y の標的図式の代表を保持する。同値性はまだ結論しない。
使われ方：導来 fiber から戻る比較射の普遍族。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

/-- 概要：運んだ合成正方形の coherence の終点を G 後の標的図式で表示する。
方針：区間交換を二度消去し、G の作用の展開公式を使う。
規約：ホモトピーの raw な射は補完した正方形の uncurry のまま。
使われ方：comma の正方形の coherence 成分。 -/
noncomputable def unitComparisonSquareCoherence {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y)
    {g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) y)}
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x y) g) :
    SSet.Homotopy (SSet.const x : (Δ[1] : SSet.{u}) ⊗ A ⟶ X)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f ≫ G) where
  h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.transportedUnitCompositionTriangle η x y f H))).h
  h₀ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.transportedUnitCompositionTriangle η x y f H))).h₀
  h₁ := by
    have h := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.transportedUnitCompositionTriangle η x y f H))).h₁
    change SSet.ι₁ ≫ _ = _ at h ⊢
    apply h.trans
    change (β_ (Δ[1] : SSet.{u}) A).hom ≫
      ((β_ A (Δ[1] : SSet.{u})).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
        (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap G _ _)) = _
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap_uncurry]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

/-- 概要：単位比較の像から comma 頂点の終辺へのホモトピーを comma の正方形へ戻す。
方針：Y の標的図式を展開し、運んだ合成正方形の coherence の二側辺を確認する。
規約：元の単位の代表と指定した終辺の代表を保持する。
使われ方：導来 fiber から戻る射を写像空間の族として構成する。 -/
noncomputable def unitCommaSquareOfComparisonHomotopy {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowFamily G x w A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaFiberSquare G x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) w A where
  target := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry f
  coherence := unitComparisonSquareCoherence η x _ f H
  target_zero := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_zero f).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex_target_const η x).symm
  target_one := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_one f).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTarget_const w).symm
  coherence_zero := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence_left (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.transportedUnitCompositionTriangle η x _ f H))
  coherence_one := by
    change _ ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.transportedUnitCompositionTriangle η x _ f H))).h = _
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowFamily_homotopy, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaVertexHomotopy] using
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence_right (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.transportedUnitCompositionTriangle η x _ f H)))

/-- 概要：復元した comma の正方形の標的族は元の写像空間の族。
方針：展開の単射性と正方形の標的の定義を使う。
規約：厳密な等式。
使われ方：逆向きの比較の射影との整合性。 -/
lemma unitCommaSquareOfComparisonHomotopy_target {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowFamily G x w A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSquareTargetFamily η x w (unitCommaSquareOfComparisonHomotopy η x w f H) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSquareTargetFamily_uncurry]
  rfl

/-- 概要：単位比較の像から指定終辺へのホモトピーを comma の写像空間の族に戻す。
方針：復元した正方形を、厳密な族の全単射の逆で読む。
規約：まだ順方向の比較との逆関係や同値性を主張しない。
使われ方：導来 fiber の普遍族を入力として戻る射を得る。 -/
noncomputable def unitCommaMappingFamilyOfComparisonHomotopy {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowFamily G x w A)) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) w :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquareEquiv G x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) w A).symm
    (unitCommaSquareOfComparisonHomotopy η x w f H)

/-- 概要：戻した写像空間の族の正方形表示は、復元に使った正方形そのもの。
方針：正方形と族の全単射の両逆。
規約：厳密な等式。
使われ方：戻る射の coherence と標的の回収。 -/
lemma unitCommaMappingFamilyOfComparisonHomotopy_square {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowFamily G x w A)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquare (unitCommaMappingFamilyOfComparisonHomotopy η x w f H) =
      unitCommaSquareOfComparisonHomotopy η x w f H :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberMappingSquareEquiv G x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSectionVertex η x) w A).apply_symm_apply _

/-- 概要：復元した comma の正方形を関手正方形へ戻すと、運んだ三角形から作った正方形。
方針：coherence の端点の正規化が raw な射を変えないことと curry の往復を使う。
規約：図式全体の厳密な等式。
使われ方：戻る射が合成三角形の輸送の coherence を保持することの検証。 -/
lemma unitCommaSquareOfComparisonHomotopy_functorSquare {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌)
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
    (H : SSet.Homotopy (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowFamily G x w A)) :
    (unitCommaSquareOfComparisonHomotopy η x w f H).functorSquare =
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorSquareOfCompositionTriangle (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.transportedUnitCompositionTriangle η x _ f H)).diagram :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.functorSquareCoherence_recover _

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories

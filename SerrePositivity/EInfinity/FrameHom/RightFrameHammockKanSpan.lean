module

public import SerrePositivity.EInfinity.FrameHom.RightFrameHammockFamily
public import SerrePositivity.EInfinity.FrameHom.KanHomFamily

/-!
概要：元の right frame と hammock の全比較を同じ六本の弱自然変換で露出する。
方針：混合 Hom・全要素 nerve・次数零置換の元の全図式を同じ宇宙で並べる。
規約：全比較は実射の自然変換であり、単に点ごとの同値を選ばない。
使われ方：関手 ∞ 圏の全同型と零単体正規化への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra Hammock SSet
open SerrePositivity.Reedy
open SerrePositivity.SimplicialModel SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C}
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)

/-- 概要：同じ元の六つの全比較の七つの全標的図式。
方針：元の right Hom、混合 Hom、source Hom、要素 nerve、hammock を同じ宇宙で並べる。
規約：元の図式の全作用素。使われ方：coherent な全弱比較。 -/
def rightFrameHammockFamilyDiagram : Fin 7 → C ⥤ SSet.{max u v}
  | 0 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ SSet.uliftFunctor.{max u v, v}
  | 1 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X ⋙ SSet.uliftFunctor.{max u v, v}
  | 2 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedFamily q r ⋙ SSet.uliftFunctor.{max u v, v}
  | 3 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom q.obj ⋙ SSet.uliftFunctor.{max u v, v}
  | 4 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ sourceFrameElementsFamily q
  | 5 => _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r ⋙ hammockHomFamily (weakEquivalences C) X
  | 6 => hammockHomFamily (weakEquivalences C) X

/-- 概要：元の六つの弱比較の始域添字。
方針：元の三つの逆向き比較を保持する。
規約：指定順序。使われ方：実比較の向きの保持。 -/
def rightFrameHammockEdgeSource : Fin 6 → Fin 7
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 4 | 5 => 6

/-- 概要：元の六つの弱比較の終域添字。
方針：元の混合 Hom と全要素比較を共通標的で読む。
規約：指定順序。使われ方：全自然変換の厳密な型。 -/
def rightFrameHammockEdgeTarget : Fin 6 → Fin 7
  | 0 => 1 | 1 => 2 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 5

/-- 概要：同じ六つの実弱比較を全標的の自然変換として公開する。
方針：元の単位・混合比較・要素 augmentation・roof を同じ順に使う。
規約：元の全単体の実射。使われ方：関手 ∞ 圏に移す比較辺。 -/
def rightFrameHammockFamilyEdge : (i : Fin 6) →
    rightFrameHammockFamilyDiagram q r (rightFrameHammockEdgeSource i) ⟶
      rightFrameHammockFamilyDiagram q r (rightFrameHammockEdgeTarget i)
  | 0 => Functor.whiskerRight
      (Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X))
      SSet.uliftFunctor
  | 1 => Functor.whiskerRight
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedRight q r)) SSet.uliftFunctor
  | 2 => Functor.whiskerRight
      (Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedLeft q r)) SSet.uliftFunctor
  | 3 => Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r) (sourceFrameElementsAugmentation q)
  | 4 => Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement r) (sourceRoofFamily q)
  | 5 => Functor.whiskerRight (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r)
      (hammockHomFamily (weakEquivalences C) X)

variable [IsCofibrant X]
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
include cof in
/-- 概要：同じ全自然変換の全成分自身は弱ホモトピー同値。
方針：同じ混合比較・実 roof・元の弱単位の反転性を使う。
規約：第一分解と指定 right frame。使われ方：coherent な全族の反転判定。 -/
lemma rightFrameHammockFamilyEdge_weak (i : Fin 6) (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ((rightFrameHammockFamilyEdge q r i).app Y) := by
  apply AnodyneWeakDetection.isWeakHomotopyEquivalence
  fin_cases i
  · exact UniverseLift.anodyneQ_map_isIso_of_small _
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_map_isIso r X ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit_trivialCofibration r Y).2 AnodyneHomotopy.anodyneQ
        (Localization.inverts _ SSet.anodyneExtensions))
  · exact UniverseLift.anodyneQ_map_isIso_of_small _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedRight_isIso q r _)
  · have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement_isFibrant r Y
    exact UniverseLift.anodyneQ_map_isIso_of_small _ (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightMixedLeft_isIso q r _)
  · exact SimplexTerminalNerve.liftedAugmentation_localized_isIso _
  · have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacement_isFibrant r Y
    exact anodyneQ_map_isIso_of_weak _
      (resolutionLeftRoofColimitMap_isWeakHomotopyEquivalence_of_first q _ r cof)
  · exact (WeakArrow.postcompositionIso ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit r).app Y)
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameReplacementUnit_trivialCofibration r Y).2 X AnodyneHomotopy.anodyneQ
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom

/-- 概要：同じ七つの全図式を同じ Kan 化の空間値図式へ送る。
方針：元の全圏の宇宙を揃え、全図式へ同じ Ex∞ を適用する。
規約：全標的を保持。使われ方：coherent な全比較の始終域。 -/
def rightFrameHammockKanDiagram (i : Fin 7) : AsSmall.{max u v} C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{max u v} :=
  AsSmall.down ⋙ kanHomFamily (rightFrameHammockFamilyDiagram q r i)

/-- 概要：同じ実全自然変換を同じ Kan 化の全自然変換にする。
方針：元の全成分へ一つの Ex∞ 関手を適用する。
規約：同じ図式・同じ順序。使われ方：coherent な比較辺の公開入力。 -/
def rightFrameHammockKanEdge (i : Fin 6) :
    rightFrameHammockKanDiagram q r (rightFrameHammockEdgeSource i) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      rightFrameHammockKanDiagram q r (rightFrameHammockEdgeTarget i) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  Functor.whiskerLeft AsSmall.down (kanHomFamilyMap (rightFrameHammockFamilyEdge q r i))

omit [IsCofibrant X] in
/-- 概要：同じ Kan 化した各全図式の値は Kan 複体。
方針：同じ Ex∞ の全値の Kan 性を使う。
規約：全標的と全中間図式。使われ方：QCat 同値判定の型の照合。 -/
lemma rightFrameHammockKanDiagram_kanComplex (i : Fin 7) (Y : AsSmall.{max u v} C) :
    KanComplex ((rightFrameHammockKanDiagram q r i ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj Y) := by
  change KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj
    ((rightFrameHammockFamilyDiagram q r i).obj (AsSmall.down.obj Y)))
  infer_instance
attribute [local instance] rightFrameHammockKanDiagram_kanComplex

include cof in
/-- 概要：同じ六つの Kan 比較の全成分は QCat 同値。
方針：元の弱比較を同じ Ex∞ と Kan Whitehead 判定で送る。
規約：実比較射を保持。使われ方：全関手 ∞ 圏の可逆な比較辺。 -/
lemma rightFrameHammockKanEdge_isQCatEquivalence (i : Fin 6) (Y : AsSmall.{max u v} C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((rightFrameHammockKanEdge q r i).app Y) := by
  exact kanHomFamilyMap_isQCatEquivalence _ (rightFrameHammockFamilyEdge_weak q r cof i) _

end SerrePositivity.EInfinity.FrameHom

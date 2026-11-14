module

public import SerrePositivity.EInfinity.FrameHom.RightFrameHammockCoherent
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan
public import SerrePositivity.EInfinity.Hammock.AsSmallComparison
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ModelRelative
public import SerrePositivity.EInfinity.SimplicialLocalization.KanHammockHomPinched

/-!
概要：同じ全標的比較の六辺から元の right Hom と同じ全圏 hammock の実 pinched 同値を得る。
方針：同じ元の六つの Kan 比較・Ex∞ 単位・宇宙同型・coherent Hom 比較を合成する。
規約：coherent 全族の構成を保持し、hammock の局所化普遍性とは分ける。
使われ方：指定局所化への全比較の同じ成分と実 QCat 同値性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory HomotopicalAlgebra SSet Opposite Hammock
open SerrePositivity.Reedy SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open SimplicialLocalization
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [ModelCategory C] {X : C} [IsCofibrant X]
  (q : CofibrantResolution (C := C) simplex X)
  (r : CofibrantResolutionFamily (C := Cᵒᵖ) simplex)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))
attribute [local instance] rightFrameHammockKanDiagram_kanComplex _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_kanComplex

/-- 概要：同じ全比較の指定六辺の実 Kan 成分を QCat 同値に束ねる。
方針：同じ元の射の同値性をそのまま束ねる。
規約：順射を変更しない。使われ方：全比較の同じ成分の合成。 -/
def rightFrameHammockKanEdgeEquivalence (i : Fin 6) (Y : AsSmall.{max u v} C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      ((rightFrameHammockKanDiagram q r (rightFrameHammockEdgeSource i)).obj Y).obj
      ((rightFrameHammockKanDiagram q r (rightFrameHammockEdgeTarget i)).obj Y).obj :=
  (rightFrameHammockKanEdge_isQCatEquivalence q r cof i Y).choose

/-- 概要：六辺の各同値の順射は元の同じ全自然変換の成分。
方針：QCat 同値の束ねの定義を読む。
規約：実射の厳密な等式。使われ方：coherent 全比較の各辺との照合。 -/
lemma rightFrameHammockKanEdgeEquivalence_hom (i : Fin 6) (Y : AsSmall.{max u v} C) :
    (rightFrameHammockKanEdgeEquivalence q r cof i Y).hom =
      (rightFrameHammockKanEdge q r i).app Y := rfl

/-- 概要：同じ coherent 全比較の六辺の実 QCat 同値を同じ順序で合成する。
方針：元の三つの逆向き辺だけを反転する。
規約：全図式の同じ六辺を使う。使われ方：実 frame→pinched 成分の入力。 -/
def rightFrameHammockKanComponentEquivalence (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (SSet.uliftFunctor.{max u v, v}.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph (weakEquivalences C) X Y)) :=
  (rightFrameHammockKanEdgeEquivalence q r cof 0 (AsSmall.up.obj Y)).trans
    ((rightFrameHammockKanEdgeEquivalence q r cof 1 (AsSmall.up.obj Y)).trans
      ((rightFrameHammockKanEdgeEquivalence q r cof 2 (AsSmall.up.obj Y)).symm.trans
        ((rightFrameHammockKanEdgeEquivalence q r cof 3 (AsSmall.up.obj Y)).symm.trans
          ((rightFrameHammockKanEdgeEquivalence q r cof 4 (AsSmall.up.obj Y)).trans
            (rightFrameHammockKanEdgeEquivalence q r cof 5 (AsSmall.up.obj Y)).symm))))

/-- 概要：元の Kan right frame Hom の同じ Ex∞ 単位は QCat 同値。
方針：元の right Hom の Kan 性と同じ anodyne 単位を使う。
規約：元の標的の fibrancy は不要。使われ方：元の Hom への復帰。 -/
def rightFrameHomExUnitEquivalence (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (SSet.uliftFunctor.{max u v, v}.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (SSet.uliftFunctor.{max u v, v}.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y))) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom_kanComplex r X Y
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app
      (SSet.uliftFunctor.{max u v, v}.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y))) :=
    AnodyneWeakDetection.isWeakHomotopyEquivalence _
      (SSet.anodyneExtensions.Q_inverts _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit_anodyne _))
  have hx := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence.isSimplicialHomotopyEquivalence
    (A := SSet.uliftFunctor.{max u v, v}.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y))
    (B := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj (SSet.uliftFunctor.{max u v, v}.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y))) h
  exact hx.isQCatEquivalence.choose

/-- 概要：元の right Hom と同じ全モデル圏の hammock pinched Hom の実 QCat 同値。
方針：同じ六辺の比較と同じ宇宙同型・元の coherent Hom 比較を合成する。
規約：元の source/target 局所化頂点を保持する。
使われ方：局所化普遍性の供給後の指定二胞体による輸送。 -/
def rightFrameHammockPinchedEquivalence (Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (SSet.uliftFunctor.{max u v, v}.obj ((_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightFrameHom r X).obj Y))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
        ((hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)).app (op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X)))
        ((hammockLocalizationNerveMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)).app (op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)))) := by
  let e := (rightFrameHomExUnitEquivalence r Y).trans
    (rightFrameHammockKanComponentEquivalence q r cof Y)
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.mapIso (AsSmallComparison.colimitIso (weakEquivalences C) X Y))
  have hp := kanHammockHomPinchedMap_weak (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y)
  exact e.trans (b.trans hp.isSimplicialHomotopyEquivalence.isQCatEquivalence.choose)

/-- 概要：元の right Hom から pinched Hom への実比較を同じ四段の射へ回収する。
方針：同じ Ex∞ 単位・六辺の成分・宇宙同型・coherent Hom 比較を展開する。
規約：元の射と元の局所化頂点。使われ方：全二胞体と零単体の追跡。 -/
lemma rightFrameHammockPinchedEquivalence_factor (Y : C) :
    (rightFrameHammockPinchedEquivalence q r cof Y).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app _ ≫ (rightFrameHammockKanComponentEquivalence q r cof Y).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (AsSmallComparison.colimitIso (weakEquivalences C) X Y).hom ≫
          kanHammockHomPinchedMap (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeCategory C)
            (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C X) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.modelRelativeObject C Y) := by
  change (_ ≫ _) ≫ (_ ≫ _) = _
  simp only [Category.assoc]
  rfl

end SerrePositivity.EInfinity.FrameHom

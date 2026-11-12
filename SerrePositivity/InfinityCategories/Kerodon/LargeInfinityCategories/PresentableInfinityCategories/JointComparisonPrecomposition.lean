module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SectionBaseChangeComposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StraighteningBaseChangeRestriction

/-!
概要：共同図式比較の豊穣前合成を、元の共同族のパラメーター前合成へ同定する。
方針：全共同単体で同じ対角比較を計算し、指定比較辺の像を回収する。
規約：元の比較と元の豊穣関手を保持する。
使われ方：P-12 の二段底変換の共同実現を元の指定同型の合成へ戻す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：豊穣前合成後の共同評価は、元の共同評価のパラメーター前合成。
方針：全添字と coherent な全対象の各単体で評価する。
規約：頂点に制限しない。使われ方：共同比較の制限後の両端の同定。 -/
lemma jointEvaluation_precompose
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] (D : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J)
    (H : EnrichedFunctor SSet.{u} L C) :
    (D.precompose H).jointEvaluation =
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap H) ≫
        D.jointEvaluation := by
  rfl

/-- 概要：前合成した共同比較族は、元の比較族の同じパラメーター制限。
方針：元の豊穣比較の全単体の対角評価を計算する。
規約：元の比較族を選び直さない。使われ方：指定比較辺の前合成の回収。 -/
lemma jointComparisonFamily_precompose
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (H : EnrichedFunctor SSet.{u} L C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonPrecompose η H).jointComparisonFamily =
      (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap H) ≫
        η.jointComparisonFamily := by
  rfl

/-- 概要：前合成した元の共同比較辺は、元の比較辺の内部前合成による像。
方針：共同族の前合成公式を転置し、添字辺の像を計算する。
規約：一単体そのものの厳密な等式。
使われ方：前合成した比較の実現と指定同型の前合成の比較。 -/
lemma jointComparisonEdge_precompose_edge
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (H : EnrichedFunctor SSet.{u} L C) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonPrecompose η H).jointComparisonEdge.edge =
      (η.jointComparisonEdge.map
        ((pre (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) ⊗ₘ
          _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap H)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})).edge := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonPrecompose η H).jointComparisonFamily).app
      (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonIndexEdge.edge =
    (((pre (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap H)).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}).app (Opposite.op ⦋1⦌))
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.transposeFunctorFamily η.jointComparisonFamily).app
          (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentResolutionComparisonIndexEdge.edge)
  rw [jointComparisonFamily_precompose, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transposeFunctorFamily_comp]
  rfl

/-- 概要：正規化した Hom 作用は、元の辺の像の指定端点移送で表される。
方針：端点移送の Hom 類の式と、ホモトピー圏の辺の像の式を使う。
規約：元の辺を保持する。使われ方：共同比較辺の前合成の正規化。 -/
lemma normalizedVertexHomMap_homMk {X Y : SSet.{u}} (f : X ⟶ Y)
    {x y : X _⦋0⦌} {x' y' : Y _⦋0⦌}
    (hx : x' = f.app (Opposite.op ⦋0⦌) x)
    (hy : y' = f.app (Opposite.op ⦋0⦌) y) (e : SSet.Edge x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap f hx hy (Truncated.HomotopyCategory.homMk e.toTruncated) =
      Truncated.HomotopyCategory.homMk ((e.map f).ofEq hx.symm hy.symm).toTruncated := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homMk_edge_ofEq]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap, SSet.hoFunctor_map, Functor.toCatHom_toFunctor,
    SSet.mapHomotopyCategory_map_homMk]
  rfl

/-- 概要：前合成した Hom の端点移送は同じ内部前合成の正規化作用。
方針：両端の図式等式を消去して一般の定義を比較する。
規約：元の Hom を保持する。使われ方：大きい共同比較の端点移送の分離。 -/
lemma kanFunctorHomCongr_precompose_normalized {A B X : SSet.{u}}
    (q : B ⟶ A) {F G : A ⟶ X} {F' G' : B ⟶ X}
    (hF : q ≫ F = F') (hG : q ≫ G = G') (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hF hG (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom q α) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap ((pre q).app X) (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hF.symm)
        (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hG.symm) α := by
  subst F' G'
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, eqToIso_refl,
    Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：指定同型の前合成の順方向は同じ指定 Hom の前合成。
方針：両表示を未正規化の同じ関手の像へ戻す。
規約：元の同型を使う。使われ方：共同比較同型の端点移送の正規化。 -/
lemma functorIsoPrecomp_hom {W X Y : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (q : W ⟶ X) :
    (e.precomp q).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom q e.hom := by
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (q ≫ f) =
      ((pre q).app Y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := rfl
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (q ≫ g) =
      ((pre q).app Y).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g) := rfl
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.vertexIso_hom_heq hx hy (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorIsoPrecomp_heq_map e q)
  exact eq_of_heq (h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.normalizedVertexHomMap_heq ((pre q).app Y) hx hy e.hom).symm)

/-- 概要：指定同型の図式等式による移送の順方向は指定 Hom の同じ移送。
方針：等式同型の合成を展開して両側の共役を比較する。
規約：元の同型を保持する。使われ方：共同比較同型を Hom の公式で比較する。 -/
lemma diagramIsoCongr_hom {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (hf : f = f') (hg : g = g') (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr hf hg e).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr hf hg e.hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr, Iso.trans_hom, Iso.symm_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr, Iso.homCongr_apply, Category.assoc]

/-- 概要：共同比較の元の Hom の前合成は、前合成した共同比較の Hom。
方針：元の比較辺の前合成の式を同じ端点へ移送する。
規約：全図式の指定 Hom の等式。使われ方：共同比較実現の前合成の同定。 -/
lemma jointComparisonHom_precompose
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (H : EnrichedFunctor SSet.{u} L C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanFunctorHomCongr (jointEvaluation_precompose D H).symm
      (jointEvaluation_precompose E H).symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.precomposeFunctorHom
        (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap H)
        (Truncated.HomotopyCategory.homMk η.jointComparisonEdge.toTruncated)) =
      Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonPrecompose η H).jointComparisonEdge.toTruncated := by
  rw [kanFunctorHomCongr_precompose_normalized, normalizedVertexHomMap_homMk]
  apply congrArg Truncated.HomotopyCategory.homMk
  apply Truncated.Edge.ext
  exact (jointComparisonEdge_precompose_edge η H).symm

/-- 概要：元の共同比較同型の前合成は、前合成した比較の指定同型。
方針：順方向の Hom の前合成の式を両端の図式等式で正規化する。
規約：元の同型を選び直さない。使われ方：二段底変換の共同実現の照合。 -/
lemma jointComparisonIso_precompose
    {C L : Type (u + 1)} [Category.{u} C] [SimplicialCategory C]
    [Category.{u} L] [SimplicialCategory L]
    {J : Type u} [Category.{u} J] {D E : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagram C J}
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanEnrichedDiagramComparison D E) (H : EnrichedFunctor SSet.{u} L C)
    (hη : ∀ j (p : C), _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence
      (X := ((D.obj j).obj p).obj) (Y := ((E.obj j).obj p).obj) ((η.component j).val p)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonPrecompose η H).jointComparisonIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.jointComparisonPrecompose_isQCatEquivalence η H hη) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.diagramIsoCongr (jointEvaluation_precompose D H).symm
        (jointEvaluation_precompose E H).symm
        ((η.jointComparisonIso hη).precomp
          (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (nerve J)) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap H)) := by
  apply Iso.ext
  rw [diagramIsoCongr_hom, functorIsoPrecomp_hom]
  symm
  exact jointComparisonHom_precompose η H

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

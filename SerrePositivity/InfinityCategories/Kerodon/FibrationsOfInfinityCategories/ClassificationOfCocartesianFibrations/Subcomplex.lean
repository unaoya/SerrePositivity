module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianNerveHornPullback
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.DiagramExtensionTransfer
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ReplacementFinalHorn

/-!
概要：scaffold による部分底の逆像の比較と、模型上の外ホーンの充填の移送。
方針：逆像部分複体を標準 pullback と同定し、任意底変換後の比較を使う。
規約：可逆化条件は模型の終端辺の族に明示し、cartesian 性を仮定しない。
使われ方：相対指数の特殊な辺の cartesian 性を実際の逆像で検証する準備。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：底を保つ scaffold の比較射は部分底の逆像部分複体にも射を誘導する。
方針：両逆像の標準 pullback 同型の間で overPullbackMap を使う。
規約：射影の充填性は定義には不要。
使われ方：部分底での図式を strict な replacement 上へ戻す。 -/
def cocartesianScaffoldSubcomplexMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (A : (nerve C).Subcomplex) :
    (A.preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) : SSet.{u}) ⟶ (A.preimage p : SSet.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.subcomplexInverseImage_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) A).isoPullback.hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap (Over.homMk (U := Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F))
      (V := Over.mk p) l h) (Over.mk A.ι) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.subcomplexInverseImage_isPullback p A).isoPullback.inv

/-- 概要：部分逆像の比較を全体へ含めると元の scaffold の比較になる。
方針：pullback の両同型の包含後の式と overPullbackMap の射影を計算する。
規約：厳密な射の可換性。
使われ方：図式の延長を模型から移す比較四角形。 -/
lemma cocartesianScaffoldSubcomplexMap_ι {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (A : (nerve C).Subcomplex) :
    cocartesianScaffoldSubcomplexMap p F l h A ≫ (A.preimage p).ι =
      (A.preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).ι ≫ l := by
  simp only [cocartesianScaffoldSubcomplexMap, Category.assoc, IsPullback.isoPullback_inv_snd]
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMap_snd]
  exact (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.subcomplexInverseImage_isPullback
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) A).isoPullback_hom_snd_assoc l

/-- 概要：cocartesian scaffold の部分逆像の比較は前合成同値。
方針：任意底変換の比較を二つの標準 pullback 同型で移す。
規約：部分底 A 自体の quasicategory 性は不要。
使われ方：外ホーンの模型の充填を元の逆像へ移す。 -/
lemma CocartesianScaffold.subcomplexMap_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    {p : E ⟶ nerve C} [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {F : C ⥤ SSet.{u}}
    [∀ c, Quasicategory (F.obj c)] {l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E}
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold p F l) (A : (nerve C).Subcomplex) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (cocartesianScaffoldSubcomplexMap p F l hs.projection A) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.subcomplexInverseImage_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) A).isoPullback).comp
    ((hs.overPullback_isPrecompositionEquivalence p F l hs.projection A.ι).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.subcomplexInverseImage_isPullback p A).isoPullback.symm))

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold export _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianScaffold (subcomplexMap_isPrecompositionEquivalence)


/-- 概要：模型の終端辺の族が可逆なら実際の cocartesian fibration の外ホーン上の図式を延長できる。
方針：replacement 上で充填し、部分と全体の scaffold 比較を通じて厳密な延長へ移す。
規約：模型での可逆化条件を明示する。実際の cocartesian 辺からの判定は後続で行う。
使われ方：cartesian ホーンの持ち上げの最後の模型変更。 -/
lemma exists_kanCocartesianFinalHorn_extension_of_model (n : ℕ) {E D : SSet.{u}}
    [Quasicategory D] (p : E ⟶ nerve (ULift.{u} (Fin (n + 3)))) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (H : ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p : SSet.{u}) ⟶ D)
    (he : let F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p
      let a := cocartesianScaffoldSubcomplexMap p F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold p)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_projection p) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2)))
      ∀ x : (F.obj (ULift.up 0)) _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.replacementFinalHornDiagram n F (a ≫ H)).app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)))) :
    ∃ G : E ⟶ D, ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p).ι ≫ G = H := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn.{u} (n + 2) (Fin.last (n + 2))
  let a := cocartesianScaffoldSubcomplexMap p F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_projection p) A
  obtain ⟨G', hG'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_kanReplacementFinalHorn_extension n F (a ≫ H) he
  exact _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Diagrams.exists_kanDiagramExtension_of_comparison (A.preimage p).ι
    (A.preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)).ι a (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold p)
    (cocartesianScaffoldSubcomplexMap_ι p F _ _ A)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_isCocartesianScaffold p).subcomplexMap_isPrecompositionEquivalence A)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_isPrecompositionEquivalence p) H G' hG'

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

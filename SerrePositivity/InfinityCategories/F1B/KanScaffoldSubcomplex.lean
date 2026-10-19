module

public import SerrePositivity.InfinityCategories.F1B.KanCocartesianNerveHornPullback
public import SerrePositivity.InfinityCategories.F1B.KanDiagramExtensionTransfer
public import SerrePositivity.InfinityCategories.F1B.KanReplacementFinalHorn

/-!
概要：scaffold による部分底の逆像の比較と、模型上の外ホーンの充填の移送。
方針：逆像部分複体を標準 pullback と同定し、任意底変換後の比較を使う。
規約：可逆化条件は模型の終端辺の族に明示し、cartesian 性を仮定しない。
使われ方：相対指数の特殊な辺の cartesian 性を実際の逆像で検証する準備。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底を保つ scaffold の比較射は部分底の逆像部分複体にも射を誘導する。
方針：両逆像の標準 pullback 同型の間で overPullbackMap を使う。
規約：射影の充填性は定義には不要。
使われ方：部分底での図式を strict な replacement 上へ戻す。 -/
def kanScaffoldSubcomplexMap {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (A : (nerve C).Subcomplex) :
    (A.preimage (simplicialReplacementProjection F) : SSet.{u}) ⟶ (A.preimage p : SSet.{u}) :=
  (kanSubcomplexInverseImage_isPullback (simplicialReplacementProjection F) A).isoPullback.hom ≫
    overPullbackMap (Over.homMk (U := Over.mk (simplicialReplacementProjection F))
      (V := Over.mk p) l h) (Over.mk A.ι) ≫
      (kanSubcomplexInverseImage_isPullback p A).isoPullback.inv

/-- 概要：部分逆像の比較を全体へ含めると元の scaffold の比較になる。
方針：pullback の両同型の包含後の式と overPullbackMap の射影を計算する。
規約：厳密な射の可換性。
使われ方：図式の延長を模型から移す比較四角形。 -/
lemma kanScaffoldSubcomplexMap_ι {C : Type u} [Category.{u} C] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (A : (nerve C).Subcomplex) :
    kanScaffoldSubcomplexMap p F l h A ≫ (A.preimage p).ι =
      (A.preimage (simplicialReplacementProjection F)).ι ≫ l := by
  simp only [kanScaffoldSubcomplexMap, Category.assoc, IsPullback.isoPullback_inv_snd]
  erw [overPullbackMap_snd]
  exact (kanSubcomplexInverseImage_isPullback
    (simplicialReplacementProjection F) A).isoPullback_hom_snd_assoc l

/-- 概要：cocartesian scaffold の部分逆像の比較は前合成同値。
方針：任意底変換の比較を二つの標準 pullback 同型で移す。
規約：部分底 A 自体の quasicategory 性は不要。
使われ方：外ホーンの模型の充填を元の逆像へ移す。 -/
lemma KanCocartesianScaffold.subcomplexMap_isPrecompositionEquivalence
    {C : Type u} [Category.{u} C] {E : SSet.{u}}
    {p : E ⟶ nerve C} [CocartesianFibration p] {F : C ⥤ SSet.{u}}
    [∀ c, Quasicategory (F.obj c)] {l : simplicialReplacement F ⟶ E}
    (hs : KanCocartesianScaffold p F l) (A : (nerve C).Subcomplex) :
    IsPrecompositionEquivalence (kanScaffoldSubcomplexMap p F l hs.projection A) :=
  (isPrecompositionEquivalence_of_iso
    (kanSubcomplexInverseImage_isPullback (simplicialReplacementProjection F) A).isoPullback).comp
    ((hs.overPullback_isPrecompositionEquivalence p F l hs.projection A.ι).comp
      (isPrecompositionEquivalence_of_iso
        (kanSubcomplexInverseImage_isPullback p A).isoPullback.symm))

/-- 概要：模型の終端辺の族が可逆なら実際の cocartesian fibration の外ホーン上の図式を延長できる。
方針：replacement 上で充填し、部分と全体の scaffold 比較を通じて厳密な延長へ移す。
規約：模型での可逆化条件を明示する。実際の cocartesian 辺からの判定は後続で行う。
使われ方：cartesian ホーンの持ち上げの最後の模型変更。 -/
lemma exists_kanCocartesianFinalHorn_extension_of_model (n : ℕ) {E D : SSet.{u}}
    [Quasicategory D] (p : E ⟶ nerve (ULift.{u} (Fin (n + 3)))) [CocartesianFibration p]
    (H : ((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p : SSet.{u}) ⟶ D)
    (he : let F := kanCocartesianStrictTransportDiagram p
      let a := kanScaffoldSubcomplexMap p F (kanUniversalScaffold p)
        (kanUniversalScaffold_projection p) (replacementNerveHorn (n + 2) (Fin.last (n + 2)))
      ∀ x : (F.obj (ULift.up 0)) _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
        ((kanReplacementFinalHornDiagram n F (a ≫ H)).app (Opposite.op ⦋1⦌)
          (finalHornEdge n, PinchedHom.constant x 1)))) :
    ∃ G : E ⟶ D, ((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p).ι ≫ G = H := by
  let F := kanCocartesianStrictTransportDiagram p
  let A := replacementNerveHorn.{u} (n + 2) (Fin.last (n + 2))
  let a := kanScaffoldSubcomplexMap p F (kanUniversalScaffold p)
    (kanUniversalScaffold_projection p) A
  obtain ⟨G', hG'⟩ := exists_kanReplacementFinalHorn_extension n F (a ≫ H) he
  exact exists_kanDiagramExtension_of_comparison (A.preimage p).ι
    (A.preimage (simplicialReplacementProjection F)).ι a (kanUniversalScaffold p)
    (kanScaffoldSubcomplexMap_ι p F _ _ A)
    ((kanUniversalScaffold_isCocartesianScaffold p).subcomplexMap_isPrecompositionEquivalence A)
    (kanUniversalScaffold_isPrecompositionEquivalence p) H G' hG'

end SerrePositivity.InfinityCategories

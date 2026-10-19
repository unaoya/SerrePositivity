module

public import SerrePositivity.InfinityCategories.F1B.KanScaffoldSubcomplex
public import SerrePositivity.InfinityCategories.F1B.KanScaffoldAssemblyEdges

/-!
概要：最後の外ホーンの模型の終端辺を実際の cocartesian 辺と同定する。
方針：部分逆像の比較を包含後に計算し、水平辺の公式に渡す。
規約：可逆化を要求するのは最後の底の辺を被覆する cocartesian 辺だけ。
使われ方：相対指数の特殊辺の cartesian 性の外ホーン充填。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：有限鎖の nerve で最後の外ホーンの終端辺を表す。
方針：標準単体と nerve の同型で指定辺を送る。
規約：次元は n+2。
使われ方：外ホーンの充填で可逆化すべき底の辺の指定。 -/
def kanFinalNerveEdge (n : ℕ) : (nerve (ULift.{u} (Fin (n + 3)))) _⦋1⦌ :=
  (stdSimplex.isoNerve (n + 2)).hom.app _ (finalHornEdge n).val

/-- 概要：模型の図式を実際の全空間へ含めると、始対象からの組み立て射になる。
方針：部分逆像の比較の包含公式と、部分底の組み立ての定義を使う。
規約：scaffold の充填性や同値性はこの等式には不要。
使われ方：終端辺の cocartesian 性と底への像を計算する。 -/
lemma kanReplacementFinalHornDiagram_scaffold_ι (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 3))))
    (F : ULift.{u} (Fin (n + 3)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) :
    kanReplacementFinalHornDiagram n F
        (kanScaffoldSubcomplexMap p F l h
          (replacementNerveHorn (n + 2) (Fin.last (n + 2)))) ≫
      ((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p).ι =
      (((horn (n + 2) (Fin.last (n + 2))).ι ≫
        (stdSimplex.isoNerve (n + 2)).hom) ▷ F.obj (ULift.up 0)) ≫
        simplicialReplacementInitialAssembly F (scaffoldFiniteInitial (n + 2)) ≫ l := by
  rw [kanReplacementFinalHornDiagram, Category.assoc, Category.assoc,
    kanScaffoldSubcomplexMap_ι]
  change _ ≫ (replacementInitialSubcomplexMap F _ _ ≫ _ ≫ l) = _
  rw [← Category.assoc (replacementInitialSubcomplexMap F _ _) _ l]
  change _ ≫ (((_ ▷ _) ≫ simplicialReplacementInitialAssembly F _) ≫ l) = _
  simp only [Category.assoc]
  rfl

/-- 概要：模型の終端辺の族の実際の全空間への像は cocartesian。
方針：任意の一単体を一つの射の nerve と表し、組み立て射の水平辺公式を使う。
規約：F の係数の頂点は始対象の値に属する。
使われ方：実際の辺の可逆化から模型の外ホーンの充填を導く。 -/
lemma kanReplacementFinalHornDiagram_scaffold_cocartesian (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 3)))) [CocartesianFibration p]
    (F : ULift.{u} (Fin (n + 3)) ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)]
    (l : simplicialReplacement F ⟶ E) (hs : KanCocartesianScaffold p F l)
    (x : (F.obj (ULift.up 0)) _⦋0⦌) :
    IsCocartesianEdge p ((kanReplacementFinalHornDiagram n F
      (kanScaffoldSubcomplexMap p F l hs.projection
        (replacementNerveHorn (n + 2) (Fin.last (n + 2)))) ≫
      ((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p).ι).app _
        (finalHornEdge n, PinchedHom.constant x 1)) := by
  rw [kanReplacementFinalHornDiagram_scaffold_ι]
  change IsCocartesianEdge p ((simplicialReplacementAssembly
    (simplicialReplacementInitialCoefficient F (scaffoldFiniteInitial (n + 2))) ≫ l).app _
      (kanFinalNerveEdge n, PinchedHom.constant x 1))
  obtain ⟨c, d, f, hf⟩ := ComposableArrows.mk₁_surjective (kanFinalNerveEdge.{u} n)
  rw [hf]
  exact hs.assembly_horizontal_isCocartesian _ f x

/-- 概要：模型の終端辺の族は底の指定した最後の辺を被覆する。
方針：包含後の組み立ての射影は直積の第一射影であることを使う。
規約：係数の頂点によらず同じ底の辺を得る。
使われ方：最後の辺だけに課した可逆化条件を適用する。 -/
lemma kanReplacementFinalHornDiagram_scaffold_base (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 3))))
    (F : ULift.{u} (Fin (n + 3)) ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F)
    (x : (F.obj (ULift.up 0)) _⦋0⦌) :
    p.app (Opposite.op ⦋1⦌) ((kanReplacementFinalHornDiagram n F
      (kanScaffoldSubcomplexMap p F l h
        (replacementNerveHorn (n + 2) (Fin.last (n + 2))))).app _
          (finalHornEdge n, PinchedHom.constant x 1)).val = kanFinalNerveEdge n := by
  change ((kanReplacementFinalHornDiagram n F
    (kanScaffoldSubcomplexMap p F l h
      (replacementNerveHorn (n + 2) (Fin.last (n + 2)))) ≫
    ((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p).ι) ≫ p).app _ _ = _
  rw [kanReplacementFinalHornDiagram_scaffold_ι, Category.assoc, Category.assoc, h,
    simplicialReplacementInitialAssembly_projection]
  rfl

/-- 概要：最後の底の辺上の cocartesian 辺を可逆に送る外ホーン逆像上の図式は延長できる。
方針：模型の終端辺の族の cocartesian 性と底の計算を、模型からの延長定理へ渡す。
規約：可逆化を要求する底の辺を明示し、他の辺には条件を課さない。
使われ方：相対指数の辺の cartesian 性を証明するための実際の逆像の充填。 -/
lemma exists_kanCocartesianFinalHorn_extension (n : ℕ) {E D : SSet.{u}}
    [Quasicategory D] (p : E ⟶ nerve (ULift.{u} (Fin (n + 3)))) [CocartesianFibration p]
    (H : ((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p : SSet.{u}) ⟶ D)
    (he : ∀ s : (((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p :
        SSet.{u}) _⦋1⦌),
      IsCocartesianEdge p s.val → p.app (Opposite.op ⦋1⦌) s.val = kanFinalNerveEdge n →
        IsInvertibleEdge (edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s))) :
    ∃ G : E ⟶ D, ((replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p).ι ≫ G = H := by
  apply exists_kanCocartesianFinalHorn_extension_of_model n p H
  dsimp only
  intro x
  let F := kanCocartesianStrictTransportDiagram p
  let l := kanUniversalScaffold p
  let h := kanUniversalScaffold_projection p
  let s := (kanReplacementFinalHornDiagram n F (kanScaffoldSubcomplexMap p F l h
    (replacementNerveHorn (n + 2) (Fin.last (n + 2))))).app (Opposite.op ⦋1⦌)
      (finalHornEdge n, PinchedHom.constant x 1)
  exact he s
    (kanReplacementFinalHornDiagram_scaffold_cocartesian n p F l
      (kanUniversalScaffold_isCocartesianScaffold p) x)
    (kanReplacementFinalHornDiagram_scaffold_base n p F l h x)

end SerrePositivity.InfinityCategories

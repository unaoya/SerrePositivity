module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.Subcomplex
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.AssemblyEdges

/-!
概要：最後の外ホーンの模型の終端辺を実際の cocartesian 辺と同定する。
方針：部分逆像の比較を包含後に計算し、水平辺の公式に渡す。
規約：可逆化を要求するのは最後の底の辺を被覆する cocartesian 辺だけ。
使われ方：相対指数の特殊辺の cartesian 性の外ホーン充填。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：有限鎖の nerve で最後の外ホーンの終端辺を表す。
方針：標準単体と nerve の同型で指定辺を送る。
規約：次元は n+2。
使われ方：外ホーンの充填で可逆化すべき底の辺の指定。 -/
def finalNerveEdge (n : ℕ) : (nerve (ULift.{u} (Fin (n + 3)))) _⦋1⦌ :=
  (stdSimplex.isoNerve (n + 2)).hom.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n).val

/-- 概要：模型の図式を実際の全空間へ含めると、始対象からの組み立て射になる。
方針：部分逆像の比較の包含公式と、部分底の組み立ての定義を使う。
規約：scaffold の充填性や同値性はこの等式には不要。
使われ方：終端辺の cocartesian 性と底への像を計算する。 -/
lemma replacementFinalHornDiagram_scaffold_ι (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 3))))
    (F : ULift.{u} (Fin (n + 3)) ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.replacementFinalHornDiagram n F
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSubcomplexMap p F l h
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2)))) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p).ι =
      (((horn (n + 2) (Fin.last (n + 2))).ι ≫
        (stdSimplex.isoNerve (n + 2)).hom) ▷ F.obj (ULift.up 0)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 2)) ≫ l := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.replacementFinalHornDiagram, Category.assoc, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSubcomplexMap_ι]
  change _ ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementInitialSubcomplexMap F _ _ ≫ _ ≫ l) = _
  rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementInitialSubcomplexMap F _ _) _ l]
  change _ ≫ (((_ ▷ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly F _) ≫ l) = _
  simp only [Category.assoc]
  rfl

/-- 概要：模型の終端辺の族の実際の全空間への像は cocartesian。
方針：任意の一単体を一つの射の nerve と表し、組み立て射の水平辺公式を使う。
規約：F の係数の頂点は始対象の値に属する。
使われ方：実際の辺の可逆化から模型の外ホーンの充填を導く。 -/
lemma replacementFinalHornDiagram_scaffold_cocartesian (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 3)))) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (F : ULift.{u} (Fin (n + 3)) ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)]
    (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E) (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.CocartesianScaffold p F l)
    (x : (F.obj (ULift.up 0)) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.replacementFinalHornDiagram n F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSubcomplexMap p F l hs.projection
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2)))) ≫
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p).ι).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)) := by
  rw [replacementFinalHornDiagram_scaffold_ι]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementAssembly
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialCoefficient F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteInitial (n + 2))) ≫ l).app _
      (finalNerveEdge n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))
  obtain ⟨c, d, f, hf⟩ := ComposableArrows.mk₁_surjective (finalNerveEdge.{u} n)
  rw [hf]
  exact hs.assembly_horizontal_isCocartesian _ f x

/-- 概要：模型の終端辺の族は底の指定した最後の辺を被覆する。
方針：包含後の組み立ての射影は直積の第一射影であることを使う。
規約：係数の頂点によらず同じ底の辺を得る。
使われ方：最後の辺だけに課した可逆化条件を適用する。 -/
lemma replacementFinalHornDiagram_scaffold_base (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 3))))
    (F : ULift.{u} (Fin (n + 3)) ⥤ SSet.{u}) (l : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F ⟶ E)
    (h : l ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F)
    (x : (F.obj (ULift.up 0)) _⦋0⦌) :
    p.app (Opposite.op ⦋1⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.replacementFinalHornDiagram n F
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSubcomplexMap p F l h
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))))).app _
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)).val = finalNerveEdge n := by
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.replacementFinalHornDiagram n F
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSubcomplexMap p F l h
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2)))) ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p).ι) ≫ p).app _ _ = _
  rw [replacementFinalHornDiagram_scaffold_ι, Category.assoc, Category.assoc, h,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementInitialAssembly_projection]
  rfl

/-- 概要：最後の底の辺上の cocartesian 辺を可逆に送る外ホーン逆像上の図式は延長できる。
方針：模型の終端辺の族の cocartesian 性と底の計算を、模型からの延長定理へ渡す。
規約：可逆化を要求する底の辺を明示し、他の辺には条件を課さない。
使われ方：相対指数の辺の cartesian 性を証明するための実際の逆像の充填。 -/
lemma exists_kanCocartesianFinalHorn_extension (n : ℕ) {E D : SSet.{u}}
    [Quasicategory D] (p : E ⟶ nerve (ULift.{u} (Fin (n + 3)))) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p]
    (H : ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p : SSet.{u}) ⟶ D)
    (he : ∀ s : (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p :
        SSet.{u}) _⦋1⦌),
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p s.val → p.app (Opposite.op ⦋1⦌) s.val = finalNerveEdge n →
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌) s))) :
    ∃ G : E ⟶ D, ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))).preimage p).ι ≫ G = H := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.exists_kanCocartesianFinalHorn_extension_of_model n p H
  dsimp only
  intro x
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram p
  let l := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold p
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_projection p
  let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.replacementFinalHornDiagram n F (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianScaffoldSubcomplexMap p F l h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.replacementNerveHorn (n + 2) (Fin.last (n + 2))))).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.finalHornEdge n, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1)
  exact he s
    (replacementFinalHornDiagram_scaffold_cocartesian n p F l
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianUniversalScaffold_isCocartesianScaffold p) x)
    (replacementFinalHornDiagram_scaffold_base n p F l h x)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

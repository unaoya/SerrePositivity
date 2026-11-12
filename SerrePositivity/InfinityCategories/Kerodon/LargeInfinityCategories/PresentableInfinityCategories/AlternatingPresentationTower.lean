module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStages

/-!
概要：元の compact filtered 表示の上で全交互有限段を可算再帰する。
方針：零段を元の表示余錐の制限とし、全前置段を保持する後続選択を繰り返す。
規約：表示添字と増大余錐は再帰全体で同じものを使う。
使われ方：可算貼り合わせに渡す coherent な全有限段列。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


private lemma evenFace_zero_eq_id :
    (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace 0) : (Δ[0] : SSet.{u}) ⟶ Δ[0]) = 𝟙 _ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro x
  apply SSet.stdSimplex.obj₀Equiv.injective
  apply Fin.ext
  omega

/-- 概要：指定した元の表示段から交互再帰の零段を作る。
方針：元の表示余錐をその段へ制限する。
規約：指定表示段を変更しない。
使われ方：任意の表示段から始まる相対可算構成。 -/
def initialAlternatingPresentationStage {I : SSet.{u}} {B : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (i : I _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage D c 0 where
  index := SSet.yonedaEquiv.symm i
  diagram := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap (SSet.yonedaEquiv.symm i) ≫ D
  augmentation := c.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap (SSet.yonedaEquiv.symm i))
  even_eq := by rw [evenFace_zero_eq_id, Category.id_comp]
  augmentation_eq := by rw [evenFace_zero_eq_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id, Category.id_comp]

variable {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
  {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I]
  {B : SSet.{u + 1}} [Quasicategory B]
  (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (hD : ∀ i : I _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up i)))
  (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex)

/-- 概要：指定全交互前置段の後続分裂三角形を一つ選ぶ。
方針：compact 因子化による非空性に選択を適用する。
規約：選択結果に元の表示余錐の全整合を保持する。
使われ方：可算再帰の後続段。 -/
def alternatingPresentationSuccessorChoice {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage D c n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationSuccessor s :=
  Classical.choice (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nonempty_alternatingPresentationSuccessor hμ D c hc hD hv s)

/-- 概要：指定表示段を始端とする coherent な全交互有限段列。
方針：元の増大余錐に厳密に整合する後続選択で自然数再帰する。
規約：各段の偶数制限は元の同じ表示図式と余錐の制限。
使われ方：fiber の全可算交互表示への貼り合わせ。 -/
def alternatingPresentationTower (i : I _⦋0⦌) : ∀ n, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationStage D c n :=
  Nat.rec (initialAlternatingPresentationStage D c i)
    (fun _ s ↦ (alternatingPresentationSuccessorChoice hμ D c hc hD hv s).next)

/-- 概要：可算再帰の小さい表示前置図式は全最終面で整合する。
方針：後続選択の元の小さい余錐の固定条件を使う。
規約：全前置単体上の厳密な等式。
使われ方：元の表示添字 I 内の可算図式の貼り合わせ。 -/
lemma alternatingPresentationTower_index_front (i : I _⦋0⦌) (n : ℕ) :
    SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) ≫
      (alternatingPresentationTower hμ D c hc hD hv i (n + 1)).index =
        (alternatingPresentationTower hμ D c hc hD hv i n).index := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AlternatingPresentationSuccessor.next_index_front
    (alternatingPresentationSuccessorChoice hμ D c hc hD hv
      (alternatingPresentationTower hμ D c hc hD hv i n))

/-- 概要：可算再帰の全交互図式は元の全前置図式を厳密に保持する。
方針：各後続段の標準拡張の固定条件を適用する。
規約：全前置単体の全射を比較する。
使われ方：標的 B 内の全可算図式の貼り合わせ。 -/
lemma alternatingPresentationTower_diagram_old (i : I _⦋0⦌) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[2 * n] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingSuccessorIso n).hom) ≫
      (alternatingPresentationTower hμ D c hc hD hv i (n + 1)).diagram =
        (alternatingPresentationTower hμ D c hc hD hv i n).diagram := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.standardAlternatingExtension_old
    (alternatingPresentationSuccessorChoice hμ D c hc hD hv
      (alternatingPresentationTower hμ D c hc hD hv i n)).forward

/-- 概要：可算再帰の全増大余錐も元の前置余錐を厳密に保持する。
方針：分裂余錐の標準拡張の全固定条件を使う。
規約：元の表示余錐との整合を全高次で保持する。
使われ方：同じ標的頂点上の全可算余錐への貼り合わせ。 -/
lemma alternatingPresentationTower_augmentation_old (i : I _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[2 * n] Δ[1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.alternatingSuccessorIso n).hom) (𝟙 Δ[0]) ≫
      (alternatingPresentationTower hμ D c hc hD hv i (n + 1)).augmentation.val =
        (alternatingPresentationTower hμ D c hc hD hv i n).augmentation.val := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.standardAlternatingExtensionCocone_old _
    (alternatingPresentationSuccessorChoice hμ D c hc hD hv
      (alternatingPresentationTower hμ D c hc hD hv i n)).triangle

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：点ごとに可逆なホモトピーを、その raw な射を保って可逆 path にする。
方針：時間を第一因子へ交換して curry し、可逆辺の全部分複体へ持ち上げる。
規約：関手同型から別の代表を選び直さない。
使われ方：B1 の正方形全体の変形を、復元側と同じ境界 path を持つ輸送にする。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy

section
variable {K X : SSet.{u}} {f g : K ⟶ X} (H : SSet.Homotopy f g)
variable (hI : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H k).toTruncated)

/-- 概要：全ての垂直辺が可逆なホモトピーを可逆 path の図式へ持ち上げる。
方針：元のホモトピーを curry した射の各頂点の可逆性を照合する。
規約：始域も標的も Kan である必要はなく、点ごとの可逆性を明示的に受け取る。
使われ方：元の正方形全体の変形を実際の可逆 path として保持する。 -/
noncomputable def pointwiseHomotopyPath : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
    (curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h)) (fun k ↦ by
      unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_curry]
      have he : (((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h).app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 1)) =
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H k).edge := by
        change H.h.app (Opposite.op ⦋1⦌)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
            H.h.app (Opposite.op ⦋1⦌)
              ((SSet.Truncated.Edge.id (X := (truncation 2).obj K) k).edge,
                _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
        have ht : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
          apply stdSimplex.ext
          intro i
          fin_cases i <;> rfl
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, ht]
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr (hI k))

/-- 概要：可逆 path の包含後の射は元のホモトピーの curry そのもの。
方針：全部分複体への持ち上げの仕様。
規約：厳密な射の等式。
使われ方：境界 path の一致の検査。 -/
lemma pointwiseHomotopyPath_ι : pointwiseHomotopyPath H hI ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X =
    curry ((β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 概要：可逆 path の始点は元のホモトピーの始点。
方針：包含後の式を零端点で評価する。
規約：図式の始点を厳密に保持する。
使われ方：指定始点を持つ境界輸送との比較。 -/
lemma pointwiseHomotopyPath_zero :
    pointwiseHomotopyPath H hI ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 0 = f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint, ← Category.assoc, pointwiseHomotopyPath_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, ← Category.assoc]
  exact H.h₀

/-- 概要：可逆 path の終点は元のホモトピーの終点。
方針：包含後の式を一端点で評価する。
規約：図式の終点を厳密に保持する。
使われ方：元の comma 正方形の回収。 -/
lemma pointwiseHomotopyPath_one :
    pointwiseHomotopyPath H hI ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint X 1 = g := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint, ← Category.assoc, pointwiseHomotopyPath_ι,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval, ← Category.assoc]
  exact H.h₁

/-- 概要：可逆 path の普遍ホモトピーへの制限で元の raw なホモトピーを回収する。
方針：時間交換と curry の両逆を使う。
規約：ホモトピー類だけでなく円柱の射そのものを回収する。
使われ方：輸送との比較で元の coherence を失わないことの確認。 -/
lemma pointwiseHomotopyPath_homotopy :
    (pointwiseHomotopyPath H hI ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathHomotopy X).h = H.h := by
  let a := pointwiseHomotopyPath H hI
  change (a ▷ (Δ[1] : SSet.{u})) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) (Δ[1] : SSet.{u})).hom ≫
    uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) = _
  have hs : (a ▷ (Δ[1] : SSet.{u})) ≫ (β_ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath X) (Δ[1] : SSet.{u})).hom =
      (β_ K (Δ[1] : SSet.{u})).hom ≫ (Δ[1] : SSet.{u}) ◁ a := rfl
  rw [← Category.assoc, hs, Category.assoc, ← uncurry_natural_left,
    pointwiseHomotopyPath_ι, uncurry_curry]
  simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 概要：固定部分図式上では、持ち上げた可逆 path も定値 path となる。
方針：包含後に検査し、元の相対条件と時間交換の自然性を使う。
規約：終点だけでなく path 全体の固定条件。
使われ方：境界の三辺を固定したまま全体図式の可逆 path を作る。 -/
lemma pointwiseHomotopyPath_restriction {L : SSet.{u}} (i : L ⟶ K) (a : L ⟶ X)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      CartesianMonoidalCategory.fst L (Δ[1] : SSet.{u}) ≫ a) :
    i ≫ pointwiseHomotopyPath H hI = a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl X := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X) := by unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι; infer_instance
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι X)).mp
  rw [Category.assoc, pointwiseHomotopyPath_ι, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathRefl_ι]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry, uncurry_natural_left, uncurry_curry]
  have hs : (Δ[1] : SSet.{u}) ◁ i ≫ (β_ (Δ[1] : SSet.{u}) K).hom =
      (β_ (Δ[1] : SSet.{u}) L).hom ≫ (i ▷ (Δ[1] : SSet.{u})) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro b
    rfl
  rw [← Category.assoc, hs, Category.assoc, hH]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro b
  rfl

end

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy

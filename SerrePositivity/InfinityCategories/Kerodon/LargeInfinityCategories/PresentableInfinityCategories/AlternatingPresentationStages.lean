module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StandardFiniteAlternatingAugmentation

/-!
概要：元の filtered 表示と増大余錐を保つ全交互有限段、およびその後続選択をまとめる。
方針：小さい表示前置図式と全交互前置図式の整合を構造体の等式として保持する。
規約：後続段は元の表示添字の中で取り、元の表示余錐を固定する。
使われ方：fiber の可算交互図式の再帰。

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


/-- 概要：元の表示余錐上の全交互有限段。
方針：偶数制限が元の表示前置図式と全増大余錐に一致する条件を記録する。
規約：すべての比較は厳密な全射の等式。
使われ方：後続選択の再帰的な入力。 -/
structure AlternatingPresentationStage {I : SSet.{u}} {B : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (n : ℕ) where
  index : (Δ[n] : SSet.{u}) ⟶ I
  diagram : (Δ[2 * n] : SSet.{u + 1}) ⟶ B
  augmentation : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder diagram) _⦋0⦌
  even_eq : SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n) ≫ diagram = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap index ≫ D
  augmentation_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n)) (𝟙 Δ[0]) ≫
    augmentation.val = (c.restrict (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap index)).val

/-- 概要：全前置段を固定して後続表示段へ分裂する選択データ。
方針：元の小さい後続余錐と全 coslice の分裂三角形を記録する。
規約：元の表示脚を厳密に回収する条件も保持する。
使われ方：次の全交互段の構成。 -/
structure AlternatingPresentationSuccessor {I : SSet.{u}} {B : SSet.{u + 1}}
    {D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D} {n : ℕ}
    (s : AlternatingPresentationStage D c n) where
  index : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder s.index) _⦋0⦌
  cocone : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder s.diagram) _⦋0⦌
  forward : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder s.diagram).Edge s.augmentation cocone
  backward : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder s.diagram).Edge cocone s.augmentation
  triangle : forward.CompStruct backward (SSet.Edge.id s.augmentation)
  cocone_eq :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction s.diagram (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n))
      s.even_eq).app (Opposite.op ⦋0⦌) cocone =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageSourceCosliceIso s.index).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap s.index) D).app (Opposite.op ⦋0⦌) (ULift.up index)
  backward_eq :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction s.diagram (SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialEvenFace n))
      s.even_eq).app (Opposite.op ⦋1⦌) backward.edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.coconeTransportLeg (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sourceCosliceRestrictedCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap s.index)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageSourceCosliceIso s.index).hom D c) (ULift.up index)).edge

/-- 概要：選んだ後続分裂三角形から、同じ表示余錐上の次の全交互段を得る。
方針：標準拡張と全偶数図式・全増大余錐の比較を使う。
規約：追加の充填や表示の選び直しはしない。
使われ方：可算再帰の後続写像。 -/
def AlternatingPresentationSuccessor.next {I : SSet.{u}} {B : SSet.{u + 1}}
    {D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D} {n : ℕ}
    {s : AlternatingPresentationStage D c n} (t : AlternatingPresentationSuccessor s) :
    AlternatingPresentationStage D c (n + 1) where
  index := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageSuccessor t.index
  diagram := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.standardAlternatingExtension t.forward
  augmentation := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.standardAlternatingExtensionCocone t.forward t.triangle
  even_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.standardAlternatingExtension_even_presentation s.index D s.diagram s.even_eq
    t.forward t.index t.cocone_eq
  augmentation_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.standardAlternatingExtensionCocone_even_presentation s.index D c
    s.diagram s.even_eq t.triangle t.index t.backward_eq

/-- 概要：compact な表示頂点と増大頂点の下で全前置段の後続選択が存在する。
方針：全交互前置図式を固定する有限分裂選択を使う。
規約：元の小さい filtered 添字と元の指定余極限を入力に取る。
使われ方：可算交互構成の選択原理。 -/
lemma nonempty_alternatingPresentationSuccessor
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {I : SSet.{u}} [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ I]
    {B : SSet.{u + 1}} [Quasicategory B]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (hD : ∀ i : I _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (D.app _ (ULift.up i)))
    (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex)
    {n : ℕ} (s : AlternatingPresentationStage D c n) :
    Nonempty (AlternatingPresentationSuccessor s) := by
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap s.index ≫ D).app _ (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))) := by
    exact hD (((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageBaseMap s.index).app _
      (SSet.stdSimplex.obj₀Equiv.symm (Fin.last n))).down)
  obtain ⟨j, d, e, r, T, hd, hr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_finiteAlternating_split hμ s.index D c hc ha hv
    s.diagram s.augmentation s.even_eq s.augmentation_eq
  exact ⟨⟨j, d, e, r, T, hd, hr⟩⟩

/-- 概要：後続段の小さい前置図式は元の前置図式を延長する。
方針：元の小さい後続余錐の最終面を計算する。
規約：全前置図式の等式。
使われ方：小さい添字内の可算貼り合わせ。 -/
lemma AlternatingPresentationSuccessor.next_index_front {I : SSet.{u}} {B : SSet.{u + 1}}
    {D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ B} {c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D} {n : ℕ}
    {s : AlternatingPresentationStage D c n} (t : AlternatingPresentationSuccessor s) :
    SSet.stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front n) ≫ t.next.index = s.index :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.finiteStageSuccessor_front t.index

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

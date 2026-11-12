module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.LiftedUnderInput
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallCompactSourceSlices

/-!
概要：compact 始域 slice の指定始点を元の成分の小さい追加入力に含める。
方針：元の under 図式を小さい join に展開し、全部分包含と始域射影で送る。
規約：元の可変図式と標的への全増大余錐を保持する。
使われ方：compact 成分 comma 射影の指定始点の下の全試験。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：compact 始域 slice の元の全 slice への包含。
方針：同じ頂点条件の全部分包含を使う。
規約：元の全射を保持する。
使われ方：追加入力の全展開を元の対象上に読む。 -/
def compactSourceSliceInclusion (μ : Cardinal.{u}) {C : SSet.{u + 1}} [Quasicategory C]
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app _ v))).ι

/-- 概要：元の compact 始域 slice 包含は単射。
方針：同じ全部分包含の単射性を使う。
規約：元の全射を変えない。
使われ方：元の全成分余錐の等式を包含後の値で検出する。 -/
instance compactSourceSliceInclusion_mono (μ : Cardinal.{u})
    {C : SSet.{u + 1}} [Quasicategory C] (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    Mono (compactSourceSliceInclusion μ x) := by
  dsimp only [compactSourceSliceInclusion]
  infer_instance

variable {A K : SSet.{u}} {C : SSet.{u + 1}} [Quasicategory C]
  (μ : Cardinal.{u}) (x : (Δ[0] : SSet.{u + 1}) ⟶ C)
  {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ x}
  (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)

local notation "j" => compactSourceSliceInclusion μ x

/-- 概要：指定 compact 始点を含む小さい join 上の元の slice 図式。
方針：元の under 図式の全展開を全部分包含で送る。
規約：元の全辺と標的への射を保持する。
使われ方：成分側の追加入力の固定標的余錐。 -/
def extendedSourceSliceDiagram :
    (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.liftedUnderInputDiagram t ≫ j

/-- 概要：指定始点を含む全 compact 入力を元の対象圏で読む。
方針：同じ元の slice 図式を始域へ射影する。
規約：compact 性は元の対象圏で測る。
使われ方：追加入力付き compact 正規化表示。 -/
def extendedSourceSliceInput : (SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A K) ⟶ C :=
  extendedSourceSliceDiagram μ x t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x

/-- 概要：追加入力の元の標的への全増大余錐。
方針：同じ元の slice 図式を全展開する。
規約：元の全単体値を保持する。
使われ方：二成分の共通入力への制限比較。 -/
def extendedSourceSliceInputCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (extendedSourceSliceInput μ x t) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone (extendedSourceSliceDiagram μ x t)

/-- 概要：追加入力の右因子は元の compact 始域 slice の可変図式。
方針：元の全展開の右入力射影を全部分包含で送る。
規約：元の slice 内の全図式の等式。
使われ方：元の入力成分との厳密な同定。 -/
lemma extendedSourceSliceDiagram_right :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K) ≫ extendedSourceSliceDiagram μ x t =
      t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z ≫ j := by
  rw [extendedSourceSliceDiagram, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.liftedUnderInputDiagram_right]
  rfl

/-- 概要：元の対象圏でも追加入力の右因子は元の可変入力。
方針：slice 内の全図式の等式へ始域射影を合成する。
規約：全単体集合射の等式。
使われ方：安定な入力制限の型合わせ。 -/
lemma extendedSourceSliceInput_right :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K) ≫ extendedSourceSliceInput μ x t =
      (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z ≫ j) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x := by
  rw [extendedSourceSliceInput, ← Category.assoc, extendedSourceSliceDiagram_right]

/-- 概要：追加入力の全増大余錐を右入力に制限すると元の増大余錐を回収する。
方針：全 slice 展開の前合成公式と右入力の等式を使う。
規約：標的への全射まで厳密に保つ。
使われ方：相対交互構成の固定標的比較。 -/
lemma extendedSourceSliceInputCocone_right :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K)) (𝟙 Δ[0]) ≫
      (extendedSourceSliceInputCocone μ x t).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone (t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z ≫ j)).val := by
  change _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (extendedSourceSliceDiagram μ x t) = _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, extendedSourceSliceDiagram_right]
  rfl

/-- 概要：追加入力の全頂点は元の対象圏で compact。
方針：元の compact 始域 slice への全展開の像の頂点条件を使う。
規約：元の対象圏の compact 性を弱めない。
使われ方：追加入力付き表示を accessible 性から構成する。 -/
lemma extendedSourceSliceInput_compact :
    ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
      ((extendedSourceSliceInput μ x t).app (Opposite.op ⦋0⦌) v) := by
  intro v
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.liftedUnderInputDiagram t).app (Opposite.op ⦋0⦌) v)

/-- 概要：展開入力が元の slice 成分図式に一致すれば右制限も元の基底成分に一致する。
方針：元の slice 後合成の基底射影公式で同定する。
規約：元の引き戻しなどの全図式を取り替えない。
使われ方：成分射影の under 試験を実際の共通入力へ合わせる。 -/
lemma extendedSourceSliceInput_right_of_companion
    {A K : SSet.{u}} {X C : SSet.{u + 1}} [Quasicategory C]
    (μ : Cardinal.{u}) (x : (Δ[0] : SSet.{u + 1}) ⟶ X) (π : X ⟶ C)
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ π)}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (U : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (hU : t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z ≫ compactSourceSliceInclusion μ (x ≫ π) =
      U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x π) :
    (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K) ≫
      extendedSourceSliceInput μ (x ≫ π) t = (U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) ≫ π := by
  rw [extendedSourceSliceInput_right, hU, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.sliceOverPostcomp_projection, ← Category.assoc]

/-- 概要：同じ成分図式への一致は元の全増大余錐の右制限も同定する。
方針：元の slice 後合成の全展開を使う。
規約：元の標的への全射を厳密に保つ。
使われ方：共通入力付き比較の固定標的を合わせる。 -/
lemma extendedSourceSliceInputCocone_right_of_companion
    {A K : SSet.{u}} {X C : SSet.{u + 1}} [Quasicategory C]
    (μ : Cardinal.{u}) (x : (Δ[0] : SSet.{u + 1}) ⟶ X) (π : X ⟶ C)
    {z : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSlice μ (x ≫ π)}
    (t : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder z)
    (U : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (hU : t ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection z ≫ compactSourceSliceInclusion μ (x ≫ π) =
      U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp x π) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A K)) (𝟙 Δ[0]) ≫
      (extendedSourceSliceInputCocone μ (x ≫ π) t).val =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone π (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone U)).val := by
  rw [extendedSourceSliceInputCocone_right]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry U ≫ π
  rw [hU, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_postcomp]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

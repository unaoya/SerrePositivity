module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallRightFibrationModels
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PredicatePreimagePullback
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallCompactModels
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.LocallySmall
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexFiberIsPullbackIso
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PointSliceComparisonFiber

/-!
概要：accessible 圏の固定対象への、compact 始域を持つ全 slice に小模型を与える。
方針：compact 全部分圏上の right fibration として読み、局所小ささで各 fiber を縮小する。
規約：元の固定対象を変更せず、元の圏の厳密な単体の小ささを仮定しない。
使われ方：fiber の compact comma の小さい filtered 添字の構成。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：局所小さい圏の元の表現可能射影は小さい Kan fiber を持つ。
方針：元の pinched Hom の小模型と slice fiber の厳密な同型を合成する。
規約：固定対象は任意の点射で指定する。
使われ方：対象への comma の right fibration の分類。 -/
lemma IsLocallySmall.sliceOver_fiber_hasSmallKanModel
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall C)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C) (b : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.HasSmallKanModel (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) b) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hC b (SSet.yonedaEquiv x)
  have := hK
  refine ⟨⟨K, hK⟩, ?_⟩
  have he := e.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso b (SSet.yonedaEquiv x)))
  have hx : SSet.yonedaEquiv.symm (SSet.yonedaEquiv x) = x :=
    SSet.yonedaEquiv.symm_apply_apply x
  exact ⟨he.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (eqToIso (congrArg (fun t ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection t) b) hx)))⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsLocallySmall (sliceOver_fiber_hasSmallKanModel)


/-- 概要：固定対象への射のうち始域が μ-compact な全 slice。
方針：始域射影に沿う compact 条件の全部分逆像を取る。
規約：全辺と全高次を保持する。
使われ方：元の compact comma の成分模型。 -/
def compactSourceSlice (μ : Cardinal.{u}) {C : SSet.{u + 1}} [Quasicategory C]
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C) : SSet.{u + 1} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver x)
    (fun v ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x).app _ v))

instance compactSourceSlice_quasicategory (μ : Cardinal.{u})
    {C : SSet.{u + 1}} [Quasicategory C] (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    Quasicategory (compactSourceSlice μ x) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.fullSubcomplexOnVertices_quasicategory _ _

/-- 概要：compact 始域 slice の元の compact 全部分圏への射影。
方針：元の始域射影を全部分条件へ制限する。
規約：元の始域を厳密に保つ。
使われ方：compact comma の小模型の構成。 -/
def compactSourceSliceProjection (μ : Cardinal.{u})
    {C : SSet.{u + 1}} [Quasicategory C] (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    compactSourceSlice μ x ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} μ C :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.predicatePreimageMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ)

instance compactSourceSliceProjection_rightFibration (μ : Cardinal.{u})
    {C : SSet.{u + 1}} [Quasicategory C] (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (compactSourceSliceProjection μ x) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightFibrations.of_isPullback
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.predicatePreimage_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ)) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem⟩

/-- 概要：μ-accessible 圏の固定対象への compact 始域 slice は小模型を持つ。
方針：小さい compact 全部分模型と局所小さい全写像空間を right fibration の縮小へ渡す。
規約：元の対象を保持し、slice 全体の accessibility を仮定しない。
使われ方：fiber の compact comma の小模型の成分。 -/
lemma IsKappaAccessible.exists_smallCompactSourceSliceModel {μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A), letI := hA
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
        (compactSourceSlice μ x)) := by
  obtain ⟨K, hK, ⟨k⟩⟩ := hC.exists_smallCompactModel
  have := hK
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallRightFibrationModel_of_base_model (compactSourceSliceProjection μ x) _ k
  intro b
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.predicatePreimageMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ)) :=
    inferInstanceAs (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (compactSourceSliceProjection μ x))
  have hs := (show _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C from ⟨μ, hC⟩).isLocallySmall
    |>.sliceOver_fiber_hasSmallKanModel x b.val
  exact hs.of_equivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberIsoOfIsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.predicatePreimage_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection x)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ)) b)).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible (exists_smallCompactSourceSliceModel)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

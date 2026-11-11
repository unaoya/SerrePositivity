module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComponentCompactFamilies
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFamilySaturation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackAccessibilityDetection

/-!
概要：固定頂点写像の小さい成分を持つ引き戻しで、compact 成分の小さい全部分模型を構成する。
方針：実現された小さい代表族の同型飽和を元の compact 成分条件と同一視する。
規約：厳密な小ささは成分模型にのみ明示し、一般の presentable 圏に自動では要求しない。
使われ方：具体的な Ind 模型の引き戻しと小さい compact 生成圏の接続。

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

/-- 概要：引き戻しの compact 成分条件は元の頂点同型に関して不変。
方針：二射影で写した同型と compact 不変性を合わせる。
規約：元の引き戻しの二頂点を比較する。
使われ方：実現族の同型飽和の判定。 -/
lemma componentCompactVertex_iff_of_iso {μ : Cardinal.{u}}
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) {x y : (pullback p q) _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q y :=
  and_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso (e.map (pullback.fst p q)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso (e.map (pullback.snd p q)))

/-- 概要：compact 成分の小さい代表族の同型飽和は、元の compact 成分条件そのもの。
方針：被覆と同型不変性の両方向を使う。
規約：同じ元の引き戻し頂点上の述語の等式。
使われ方：元の全部分圏と小さい模型との全同値。 -/
lemma familySaturation_eq_componentCompact {μ : Cardinal.{u}}
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) {T : Type u} (v : T → (pullback p q) _⦋0⦌)
    (hv : ∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q (v t))
    (hc : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q x → ∃ t, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (v t))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FamilySaturation v = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q := by
  funext x
  apply propext
  constructor
  · rintro ⟨t, ⟨e⟩⟩
    exact (componentCompactVertex_iff_of_iso p q e).mpr (hv t)
  · exact hc x

/-- 概要：厳密に小さい固定頂点写像を持つ成分模型では、compact 成分の全部分圏に小さい模型がある。
方針：両成分の小ささを引き戻しへ移し、小さい実現族の同型飽和の全同値を使う。
規約：一般の presentable 引き戻しの accessibility は結論に先取りしない。
使われ方：Ind 模型上の引き戻しの小さい compact 全部分圏。 -/
lemma exists_smallComponentCompactModel_of_component_smallFixedVertexMaps
    {μ : Cardinal.{u}} {E D B : SSet.{u + 1}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ D) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsLocallySmall B)
    (hEX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps E) (hDX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps D)
    (p : E ⟶ B) (q : D ⟶ B) [InnerFibration p] :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentCompactObjects μ p q)) := by
  obtain ⟨T, v, hv, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallComponentCompactFamily hE hD hB p q
  have hX := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullback_hasSmallFixedVertexMaps p q hEX hDX
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.familySaturationCategory v = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentCompactObjects μ p q :=
    congrArg (fun P : (pullback p q) _⦋0⦌ → Prop ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (pullback p q) P).toSSet)
      (familySaturation_eq_componentCompact p q v hv hc)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModel hX v, inferInstance,
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFamilySaturationEquivalence v hX).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (eqToIso he))⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

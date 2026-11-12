module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallCompactFamilies
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFamilySaturation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Subcategory
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.CompactFunctorRestriction

/-!
概要：全 compact 対象の全部分圏に対する小さい模型を strict な accessible 圏で構成する。
方針：全 compact 対象を小さい retract 族で代表し、その同型飽和の全部分模型を使う。
規約：固定頂点写像の小ささを明示し、元の compact 全部分圏との全同値を供給する。
使われ方：引き戻しの compact な成分図式を小さい ∞ 圏で扱う。

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

/-- 概要：全 compact 対象を代表する小さい族の同型飽和は、元の compact 条件そのもの。
方針：頂点同型による compact 不変性と代表族の全射性を合わせる。
規約：同じ元の対象上の述語の等式。
使われ方：元の compact 全部分圏と小さい族の模型の同一視。 -/
lemma familySaturation_eq_kappaCompact {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] {T : Type u} (v : T → C _⦋0⦌)
    (hv : ∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (v t))
    (hcover : ∀ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ x →
      ∃ t, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (v t))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FamilySaturation v = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ := by
  funext x
  apply propext
  constructor
  · rintro ⟨t, ⟨e⟩⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso e).mpr (hv t)
  · exact hcover x

/-- 概要：strict な κ-accessible 圏の全 κ-compact 全部分圏は小さい ∞ 圏と全同値。
方針：小さい retract 代表族の同型飽和を、元の compact 全部分圏として読む。
規約：元の全辺と全高次を保持する全同値。
使われ方：Ind 模型上での引き戻しの小さい compact 図式。 -/
lemma IsKappaAccessible.exists_smallCompactModel_of_smallFixedVertexMaps {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasSmallFixedVertexMaps C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ C)) := by
  obtain ⟨T, v, hv, hc⟩ := hC.exists_smallCompactFamily
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.familySaturationCategory v = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ C :=
    congrArg (fun P : C _⦋0⦌ → Prop ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices C P).toSSet)
      (familySaturation_eq_kappaCompact v hv hc)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModel hX v, inferInstance,
    ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFamilySaturationEquivalence v hX).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (eqToIso he))⟩⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible (exists_smallCompactModel_of_smallFixedVertexMaps)


/-- 概要：一般の κ-accessible 圏の全 κ-compact 全部分圏は小さい ∞ 圏と全同値。
方針：具体的な Ind 模型で小さい compact 模型を作り、元の同値の全 compact 制限で戻す。
規約：元の圏に厳密な固定頂点写像の小ささを要求しない。
使われ方：一般の presentable 圏の compact な成分図式を小さい模型で表す。 -/
lemma IsKappaAccessible.exists_smallCompactModel {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ C)) := by
  have : Fact κ.IsRegular := ⟨hC.1⟩
  obtain ⟨A, hA, ⟨e⟩⟩ := hC.exists_indEquivalence
  have := hA
  obtain ⟨K, hK, ⟨k⟩⟩ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInfinity_isKappaAccessible κ A).exists_smallCompactModel_of_smallFixedVertexMaps
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ A)
  have := hK
  exact ⟨K, hK, ⟨k.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kappaCompactEquivalence κ e)⟩⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible (exists_smallCompactModel)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

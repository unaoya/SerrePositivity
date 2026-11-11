module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallSpanPullbackComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFullModel
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.RelativeFunctorSmallness
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.QCatPullbackLimit

/-!
概要：小さい模型を持つ三圏の引き戻しに、小さい模型を与える。
方針：共役 cospan の path 引き戻しを次数ごとに縮小し、厳密な成分比較と極限の一意性で戻す。
規約：元の圏の厳密な固定頂点写像の小ささを仮定しない。
使われ方：一般の compact 成分圏の引き戻しの小さい模型。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：次数ごとに小さい三圏の path 引き戻しも全次数で小さい。
方針：内部 Hom、全部分包含、二回の実引き戻しの公開小ささを使う。
規約：共通標的と二辺の充填性を要求しない。
使われ方：共役した小さい cospan の実際の縮小。 -/
lemma catPullback_obj_small_of_small_components {E D B : SSet.{u + 1}}
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (D.obj n)] [∀ n, Small.{u} (B.obj n)]
    (p : E ⟶ B) (q : D ⟶ B) (n : SimplexCategoryᵒᵖ) :
    Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q).obj n) := by
  have : ∀ m, Small.{u} ((Δ[1] : SSet.{u + 1}).obj m) := fun _ ↦ inferInstance
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B) :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex).ι)
  have : ∀ m, Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath B).obj m) :=
    fun m ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSmall_obj_of_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathι B) m
  have : ∀ m, Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacement p).obj m) :=
    fun m ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullback_obj_small (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint B 0) p m
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportPullback_obj_small (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) q n

/-- 概要：次数ごとに小さい三圏の path 引き戻しは小さい ∞ 圏と全同値。
方針：全次数の縮小同型を作り、ホーン充填を元の宇宙に戻す。
規約：同値でなく厳密な縮小同型から構成する。
使われ方：小さい cospan 模型の引き戻しの宇宙制御。 -/
lemma exists_smallCatPullbackModel_of_small_components {E D B : SSet.{u + 1}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    [∀ n, Small.{u} (E.obj n)] [∀ n, Small.{u} (D.obj n)] [∀ n, Small.{u} (B.obj n)]
    (p : E ⟶ B) (q : D ⟶ B) :
    ∃ (A : SSet.{u}) (hA : Quasicategory A),
      letI := hA
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q)) := by
  have : ∀ n, Small.{u} ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q).obj n) :=
    catPullback_obj_small_of_small_components p q
  let A := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSet.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallSimplicialSetIso.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q)
  have : InnerFibration e.hom := ⟨MorphismProperty.of_isIso innerFibrations _⟩
  have : Quasicategory ((SSet.uliftFunctor.{u + 1, u}).obj A) :=
    quasicategory_of_innerFibration e.hom
  have : Quasicategory A := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.quasicategory_of_ulift.{u, u + 1} A
  exact ⟨A, inferInstance, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e⟩⟩

/-- 概要：三成分が小さい模型を持つ任意の cospan の path 引き戻しは小さい模型を持つ。
方針：小さい共役 cospan の大きい宇宙での引き戻しを縮小し、二つの厳密な比較で戻す。
規約：元の大きい圏の全単体の小ささは要求しない。
使われ方：compact 成分の引き戻しの小さい模型の準備。 -/
lemma exists_smallCatPullbackModel_of_component_models
    {A K L : SSet.{u}} [Quasicategory A] [Quasicategory K] [Quasicategory L]
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) E)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj K) D)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj L) B)
    (p : E ⟶ B) (q : D ⟶ B) :
    ∃ (T : SSet.{u}) (hT : Quasicategory T),
      letI := hT
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj T) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q)) := by
  have (n : SimplexCategoryᵒᵖ) : Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj A).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (A.obj n)))
  have (n : SimplexCategoryᵒᵖ) : Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj K).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (K.obj n)))
  have (n : SimplexCategoryᵒᵖ) : Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj L).obj n) :=
    inferInstanceAs (Small.{u} (ULift.{u + 1} (L.obj n)))
  obtain ⟨T, hT, ⟨t⟩⟩ := exists_smallCatPullbackModel_of_small_components
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor e b p))
    ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallModelFunctor d b q))
  have := hT
  obtain ⟨s⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallSpanPullbackComparison e d b p q
  exact ⟨T, hT, ⟨t.trans s⟩⟩

/-- 概要：同値持ち上げを持つ元の実引き戻しと path 引き戻しは全同値。
方針：同じ cospan の二つの native 極限錐の頂点同型を元の圏の全同値へ戻す。
規約：単体集合の二つの引き戻しを厳密に同じとは扱わない。
使われ方：compact 全部分圏の実引き戻しへの模型移送。 -/
lemma exists_strictPullback_catPullback_equivalence {E D B : SSet.{u + 1}}
    [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) :
    letI := hp.innerFibration
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (pullback p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullback p q)) := by
  have : InnerFibration p := hp.innerFibration
  let E₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u + 1} := (⟨E, inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u + 1})
  let D₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u + 1} := (⟨D, inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u + 1})
  let B₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u + 1} := (⟨B, inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u + 1})
  let p₀ : E₀ ⟶ B₀ := p
  let q₀ : D₀ ⟶ B₀ := q
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackCone p₀ q₀)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.qCatPullbackInfinityCone_isLimit p₀ q₀ hp
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitVertexIso c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone p q) hc (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone_isLimit p q)
  have hpt : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackCone p₀ q₀).pt = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackObject p₀ q₀ := rfl
  have hi' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackObject p₀ q₀))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackObject p q)) := by
    simpa only [c, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.catPullbackCone_vertex,
      hpt, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex] using hi
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_qCatEquivalence_of_catInfinityVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.qCatPullbackObject p₀ q₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.catPullbackObject p q) hi'

/-- 概要：小さい模型を持つ三圏の実引き戻しは、一脚が同値を持ち上げれば小さい模型を持つ。
方針：path 引き戻しの小さい模型を native 極限比較で元の実引き戻しへ戻す。
規約：引き戻しの accessibility や固定頂点写像の小ささを仮定しない。
使われ方：一般の compact 成分圏の引き戻しの小さい模型。 -/
lemma exists_smallStrictPullbackModel_of_component_models
    {A K L : SSet.{u}} [Quasicategory A] [Quasicategory K] [Quasicategory L]
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A) E)
    (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj K) D)
    (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj L) B)
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) :
    letI := hp.innerFibration
    ∃ (T : SSet.{u}) (hT : Quasicategory T),
      letI := hT
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj T) (pullback p q)) := by
  have : InnerFibration p := hp.innerFibration
  obtain ⟨T, hT, ⟨t⟩⟩ := exists_smallCatPullbackModel_of_component_models e d b p q
  have := hT
  obtain ⟨s⟩ := exists_strictPullback_catPullback_equivalence p q hp
  exact ⟨T, hT, ⟨t.trans s.symm⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

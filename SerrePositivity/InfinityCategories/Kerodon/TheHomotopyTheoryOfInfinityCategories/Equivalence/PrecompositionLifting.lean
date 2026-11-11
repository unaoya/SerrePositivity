module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathFinalLifting
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：単射に沿う関手の同型の厳密化と前合成の境界持ち上げ。
方針：可逆ホモトピーを単射に沿って延長し、本質的全射性を頂点全射性に強める。
規約：モデル構造は用いず、既存の inner fibration の境界判定を用いる。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join 比較の貼り合わせ。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：単射上で同型な制限を持つ関手は、その制限に厳密に一致する関手に置き換えられる。
方針：同型を可逆な頂点辺を持つホモトピーで表し、単射に沿って延長する。
規約：標的だけに quasicategory 性を要求する。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM）、§4.6.2（Tag 01HM） の貼り合わせ。 -/
lemma exists_extension_of_functorIso {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (u : B ⟶ X) (v : A ⟶ X)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (i ≫ u) v) : ∃ w : B ⟶ X, i ≫ w = v := by
  let H := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.simplicialHomotopy e
  let H' := (β_ (Δ[1] : SSet.{u}) A).hom ≫ H.h
  have h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ H' = i ≫ u := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_zero_braiding]
    exact H.h₀
  have h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H' = v := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.prismEndpoint_one_braiding]
    exact H.h₁
  have hv : ∀ x : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      (H'.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1))) := by
    intro x
    have he : H'.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H x).edge := by
      change H.h.app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x 1, SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u}))) =
        H.h.app (Opposite.op ⦋1⦌)
          ((SSet.Truncated.Edge.id (X := (truncation 2).obj A) x).edge, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge)
      have hi : SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
        apply stdSimplex.ext
        intro j
        fin_cases j <;> rfl
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one, hi]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge e) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.edge_isInvertible e) x)
  obtain ⟨F, hF, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.equivalenceHomotopy_extend i H' u h₀ hv
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ F, ?_⟩
  rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hF, h₁]

/-- 概要：単射の前合成が本質的全射なら、その前合成は頂点上で全射。
方針：選んだ同型を可逆ホモトピーの延長で厳密な制限の等式にする。
規約：元の二つの単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の前合成の境界充填。 -/
lemma pre_surjective_of_essentiallySurjective {A B X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) [Mono i] (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective ((pre i).app X)) :
    Function.Surjective (((pre i).app X).app (Opposite.op ⦋0⦌)) := by
  intro v
  obtain ⟨a, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv A X).surjective v
  obtain ⟨b, ⟨e⟩⟩ := hi (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  obtain ⟨u, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B X).surjective b
  obtain ⟨w, hw⟩ := exists_extension_of_functorIso i u a e
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex w, ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ w) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a
  rw [hw]

/-- 概要：単射である前合成の同値は全境界に対する持ち上げを持つ。
方針：制限の inner fibration 性、充満忠実性、厳密化した頂点全射性を合わせる。
規約：標的 X は任意の quasicategory。
使われ方：Kerodon §4.6.2（Tag 01HM） の pushout とセルによる同値の保存。 -/
@[kerodon 01FS, kerodon 01G6]
lemma IsPrecompositionEquivalence.trivialKanFibration_pre {A B : SSet.{u}}
    {i : A ⟶ B} [Mono i] (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i)
    (X : SSet.{u}) [Quasicategory X] : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre i).app X) := by
  exact (hi X).isFullyFaithful.trivialKanFibration_of_surjective
    (pre_surjective_of_essentiallySurjective i (hi X).choose.isEssentiallySurjective)

/-- 概要：pushout を前合成の関手単体集合へ写すと pullback になる。
方針：閉対称モノイダル構造の反変内部 Hom の極限保存を使う。
規約：単体集合と標的 X は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の pushout による比較。 -/
lemma isPullback_pre_of_isPushout {A B C D : SSet.{u}}
    {i : A ⟶ B} {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D}
    (h : IsPushout i g k j) (X : SSet.{u}) :
    IsPullback ((pre j).app X) ((pre k).app X) ((pre g).app X) ((pre i).app X) :=
  h.op.map (internalHom.flip.obj X)

/-- 概要：単射である前合成の同値条件は pushout で保存される。
方針：関手単体集合の pullback で trivial Kan fibration を引き戻す。
規約：貼り合わせる射 g と元の四対象の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルによる同値の保存。 -/
lemma IsPrecompositionEquivalence.of_isPushout {A B C D : SSet.{u}}
    {i : A ⟶ B} [Mono i] {g : A ⟶ C} {k : B ⟶ D} {j : C ⟶ D}
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (h : IsPushout i g k j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence j := by
  intro X hX
  have := hi.trivialKanFibration_pre X
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre j).app X) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback (isPullback_pre_of_isPushout h X).flip
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := (pre i).app X))⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

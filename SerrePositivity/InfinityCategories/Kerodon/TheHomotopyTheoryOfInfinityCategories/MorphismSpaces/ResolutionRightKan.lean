module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionRightQuasicategory
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
概要：解像の右随伴は Kan 複体を Kan 複体へ写す。
方針：ホーンの前合成の比較を一般の射影の同値性で移し、単射に沿う厳密な延長を随伴で戻す。
規約：Fibration は全ホーンの右持ち上げ性としてだけ使い、弱同値のモデル構造は使わない。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、Corollary 4.6.7.16（Tag 01LQ）、右随伴の写像空間の Kan 性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：Kan 複体へのホーンに沿う前合成は trivial Kan fibration。
方針：境界との pushout-product の anodyne 性と内部 Hom の随伴で境界持ち上げを示す。
規約：anodyne 性は全ホーンの右持ち上げ性に対する左持ち上げ性として使う。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、右随伴のホーンの比較の元の側。 -/
lemma trivialKanFibration_pre_horn (Z : SSet.{u}) [KanComplex Z]
    (n : ℕ) (i : Fin (n + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre (horn (n + 1) i).ι).app Z) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro d
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (horn (n + 1) i).ι
    (boundary d).ι
  let sq' := Functor.PullbackObjObj.ofIsTerminal internalHom (horn (n + 1) i).ι
    (terminal.from Z) terminalIsTerminal
  change HasLiftingProperty (boundary d).ι sq'.π
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact (anodyneExtensions_pushoutObjObjι' sq (anodyneExtensions.horn_ι i))
    (terminal.from Z) (by rw [← HomotopicalAlgebra.fibration_iff]; infer_instance)

/-- 概要：解像したホーンに沿う Kan 複体への前合成は quasicategory の同値。
方針：一般の射影の自然性で前合成の正方形を作り、三辺の同値性から残りを得る。
規約：ホーンの添字は内側でも端点でもよい。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、解像したホーン上の厳密な延長。 -/
lemma coherentResolution_pre_horn_isQCatEquivalence (Z : SSet.{u}) [KanComplex Z]
    (n : ℕ) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map (horn (n + 1) i).ι)).app Z) := by
  let j := (horn (n + 1) i).ι
  haveI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre j).app Z) := trivialKanFibration_pre_horn Z n i
  have hn : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map j ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app Δ[n + 1] =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (horn (n + 1) i).toSSet ≫ j :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.naturality j
  have he : ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app Δ[n + 1])).app Z) ≫
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map j)).app Z) =
      ((pre j).app Z) ≫
        ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app (horn (n + 1) i).toSSet)).app Z) := by
    rw [← NatTrans.comp_app, ← pre_map, hn, pre_map, NatTrans.comp_app]
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll.app Δ[n + 1])).app Z) ≫
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map j)).app Z)) := by
    rw [he]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration ((pre j).app Z)).comp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence (horn (n + 1) i).toSSet Z)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionProjectionAll_isPrecompositionEquivalence Δ[n + 1] Z).cancel_left hc

/-- 概要：右随伴における任意のホーンは充填できる。
方針：随伴で解像したホーン上の射へ移し、前合成の本質的全射性を厳密化して延長する。
規約：Kan 複体 Z を入力とする。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、右随伴の Kan 性のホーン条件。 -/
lemma coherentResolutionRightAdjoint_horn_extension (Z : SSet.{u}) [KanComplex Z]
    (n : ℕ) (i : Fin (n + 2))
    (σ : (horn (n + 1) i).toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z) :
    ∃ F : Δ[n + 1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z, (horn (n + 1) i).ι ≫ F = σ := by
  let j := (horn (n + 1) i).ι
  haveI : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map j) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map_mono j
  let a := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv _ Z).symm σ
  have he := coherentResolution_pre_horn_isQCatEquivalence Z n i
  obtain ⟨v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.pre_surjective_of_essentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map j)
    he.choose.isEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)
  obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.obj Δ[n + 1]) Z).surjective v
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolution.map j ≫ g = a := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective hv
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv _ Z g, ?_⟩
  have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv _ Z) hg
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv_naturality_left] at h
  exact h.trans ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionAdjunction.homEquiv _ Z).apply_symm_apply σ)

/-- 概要：解像の右随伴は Kan 複体を Kan 複体へ写す。
方針：互換な面の族をホーンの射にまとめ、右随伴のホーン延長を適用する。
規約：全ての次数とホーン番号を扱う。
使われ方：Kerodon Theorem 4.6.7.5（Tag 01LE）、比較射の標的の Kan 性。 -/
instance coherentResolutionRightAdjoint_kanComplex (Z : SSet.{u}) [KanComplex Z] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionRightAdjoint.obj Z) := by
  rw [KanComplex.iff]
  intro n i f hf
  obtain ⟨F, hF⟩ := coherentResolutionRightAdjoint_horn_extension Z n i hf.desc
  refine ⟨F, fun j hj ↦ ?_⟩
  rw [← horn.ι_ι i j hj, Category.assoc, hF, hf.ι_desc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

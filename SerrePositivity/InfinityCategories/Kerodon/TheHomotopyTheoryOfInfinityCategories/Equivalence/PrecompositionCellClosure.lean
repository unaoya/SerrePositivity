module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionUnderPushout
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
概要：単射の前合成の同値条件の持ち上げ判定と合成列による閉包。
方針：反変内部 Hom の自己随伴で全境界持ち上げを左持ち上げ性に交換する。
規約：モデル構造と small object factorization は使用しない。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の無限のセルの貼り合わせ。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：前合成の内部 Hom の持ち上げ問題の二つの始域を交換できる。
方針：反変内部 Hom の自己随伴と反対圏の持ち上げの双対性を使う。
規約：四つの始域と標的 X は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の境界持ち上げの交換。 -/
lemma hasLiftingProperty_pre_iff_swapped {A B C D : SSet.{u}}
    (i : A ⟶ B) (j : C ⟶ D) (X : SSet.{u}) :
    HasLiftingProperty i ((pre j).app X) ↔ HasLiftingProperty j ((pre i).app X) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipAdjunction X).hasLiftingProperty_iff i j.op
  change HasLiftingProperty ((pre i).app X).op j.op ↔
    HasLiftingProperty i ((pre j).app X) at h
  exact h.symm.trans (HasLiftingProperty.iff_unop _ _)

/-- 概要：quasicategory を標的とする全ての境界の前合成の射の族。
方針：単体集合 X とその quasicategory 性および境界の次数で添字付けする。
規約：持ち上げによる補助クラスで、同値の定義は変更しない。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルの貼り合わせの閉包。 -/
def precompositionBoundaryTests : MorphismProperty SSet.{u} :=
  MorphismProperty.ofHoms (fun t : Σ X : SSet.{u}, {n : ℕ // Quasicategory X} ↦
    (pre (boundary t.2.val).ι).app t.1)

/-- 概要：単射の前合成の同値条件は全ての境界の前合成に対する左持ち上げ性と同値。
方針：全境界の trivial Kan fibration 判定と内部 Hom の持ち上げの交換を使う。
規約：単射の始域・終域の quasicategory 性は不要。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の左持ち上げクラスとしての閉包。 -/
lemma isPrecompositionEquivalence_iff_llp_boundaryTests {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i ↔ precompositionBoundaryTests.llp i := by
  constructor
  · intro hi E F p hp
    obtain ⟨⟨X, n, hX⟩⟩ := hp
    have : Quasicategory X := hX
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre i).app X) := hi.trivialKanFibration_pre X
    exact (hasLiftingProperty_pre_iff_swapped i (boundary n).ι X).2
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).1 inferInstance n)
  · intro hi X hX
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre i).app X) := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
      intro n
      apply (hasLiftingProperty_pre_iff_swapped i (boundary n).ι X).1
      have hp : precompositionBoundaryTests ((pre (boundary n).ι).app X) := by
        exact MorphismProperty.ofHoms.mk
          (f := fun t : Σ Y : SSet.{u}, {m : ℕ // Quasicategory Y} ↦
            (pre (boundary t.2.val).ι).app t.1) ⟨X, ⟨n, hX⟩⟩
      exact hi _ hp
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _

/-- 概要：単射の前合成の同値条件のクラスは単射と左持ち上げクラスの共通部分。
方針：単射ごとの持ち上げ判定をクラスの等式にする。
規約：既存の補助クラスの定義は変更しない。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の同型とセルの族による閉包。 -/
lemma monoPrecompositionEquivalences_eq_inf_llp :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u} =
      MorphismProperty.monomorphisms SSet.{u} ⊓ precompositionBoundaryTests.llp := by
  funext A B i
  apply propext
  constructor
  · intro h
    have : Mono i := h.1
    exact ⟨h.1, (isPrecompositionEquivalence_iff_llp_boundaryTests i).1 h.2⟩
  · intro h
    have : Mono i := h.1
    exact ⟨h.1, (isPrecompositionEquivalence_iff_llp_boundaryTests i).2 h.2⟩

/-- 概要：単射の前合成の同値条件のクラスは射の同型で不変。
方針：単射と左持ち上げクラスの不変性を合わせる。
規約：Arrow 圏の同型を扱う。
使われ方：Kerodon §4.6.2（Tag 01HM） の余極限の表示の変更。 -/
instance monoPrecompositionEquivalences_respectsIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u}.RespectsIso := by
  rw [monoPrecompositionEquivalences_eq_inf_llp]
  infer_instance

/-- 概要：単射の前合成の同値条件は射の retract で閉じる。
方針：単射と左持ち上げクラスの retract による閉包を使う。
規約：Arrow 圏での retract。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルによる比較。 -/
instance monoPrecompositionEquivalences_isStableUnderRetracts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u}.IsStableUnderRetracts := by
  rw [monoPrecompositionEquivalences_eq_inf_llp]
  infer_instance

/-- 概要：単射の前合成の同値条件は恒等射を含み合成で閉じる。
方針：単射と左持ち上げクラスの合成による閉包を使う。
規約：有限の合成を扱う。
使われ方：Kerodon §4.6.2（Tag 01HM） のセルによる比較。 -/
instance monoPrecompositionEquivalences_isMultiplicative :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u}.IsMultiplicative := by
  rw [monoPrecompositionEquivalences_eq_inf_llp]
  infer_instance

/-- 概要：単射の前合成の同値条件は小さい射の族の coproduct で閉じる。
方針：単射の保存と左持ち上げ性の coproduct による保存を合わせる。
規約：添字の宇宙は単体の宇宙 u。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の各次元のセルの族。 -/
instance monoPrecompositionEquivalences_isStableUnderCoproductsOfShape (J : Type u) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u}.IsStableUnderCoproductsOfShape J := by
  apply MorphismProperty.IsStableUnderCoproductsOfShape.mk
  intro A B _ _ f hf
  have : ∀ j, Mono (f j) := fun j ↦ (hf j).1
  have : Mono (Limits.Sigma.map f) := inferInstance
  refine ⟨inferInstance, (isPrecompositionEquivalence_iff_llp_boundaryTests _).2 ?_⟩
  exact MorphismProperty.colimMap _ (fun j ↦
    (isPrecompositionEquivalence_iff_llp_boundaryTests (f j.as)).1 (hf j.as).2)

/-- 概要：単射である前合成の同値条件は任意の小さい整列された合成列で閉じる。
方針：単射の合成列の閉包と左持ち上げ性の合成列の閉包を合わせる。
規約：添字の宇宙は単体集合の単体の宇宙 u、列は Mathlib の整列連続な列。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の無限の骨格の貼り合わせ。 -/
instance monoPrecompositionEquivalences_isStableUnderTransfiniteCompositionOfShape
    (J : Type u) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u}.IsStableUnderTransfiniteCompositionOfShape J where
  le := by
    intro A B i hi
    have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u} ≤ MorphismProperty.monomorphisms SSet.{u} :=
      fun _ _ _ h ↦ h.1
    have hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u} ≤ precompositionBoundaryTests.llp := by
      intro A B i h
      have : Mono i := h.1
      exact (isPrecompositionEquivalence_iff_llp_boundaryTests i).1 h.2
    have hm' := (MorphismProperty.transfiniteCompositionsOfShape_monotone J hm) _ hi
    have hmono : Mono i :=
      (MorphismProperty.monomorphisms SSet.{u}).transfiniteCompositionsOfShape_le J _ hm'
    have hl' := (MorphismProperty.transfiniteCompositionsOfShape_monotone J hl) _ hi
    exact ⟨hmono, (isPrecompositionEquivalence_iff_llp_boundaryTests i).2
      (precompositionBoundaryTests.llp.transfiniteCompositionsOfShape_le J _ hl')⟩

/-- 概要：単射の前合成の同値条件は宇宙 u の全ての整列合成列で閉じる。
方針：各整列型に対する保存を束ねる。
規約：小さい余極限に対する閉包。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） のセル分解。 -/
instance monoPrecompositionEquivalences_isStableUnderTransfiniteComposition :
    MorphismProperty.IsStableUnderTransfiniteComposition.{u}
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u} where

/-- 概要：単射の前合成の同値条件は自然数で添字付けた整列連続な合成列で閉じる。
方針：宇宙 u の合成列の閉包を可算の宇宙へ縮小する。
規約：終点は与えた列の余極限。
使われ方：Kerodon Lemma 4.6.2.10（Tag 01HX） の無限の骨格。 -/
instance monoPrecompositionEquivalences_isStableUnderSequentialComposition :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u}.IsStableUnderTransfiniteCompositionOfShape ℕ := by
  have := MorphismProperty.IsStableUnderTransfiniteComposition.shrink₀
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.monoPrecompositionEquivalences.{u}
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

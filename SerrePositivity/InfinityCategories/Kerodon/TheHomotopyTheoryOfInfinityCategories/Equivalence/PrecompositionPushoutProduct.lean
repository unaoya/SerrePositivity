module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionLifting
public import Mathlib.CategoryTheory.Adhesive.PushoutProduct

/-!
概要：前合成の同値条件の pushout-product による保存。
方針：直積と pushout による保存を二対三則で結ぶ。
規約：同値条件を課す因子は単射とする。
使われ方：Kerodon §4.6.2（Tag 01HM） の部分を固定した可逆な円柱。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：単射である前合成の同値条件は任意の射との pushout-product に移る。
方針：片側の包含を同値の直積の pushout として扱い、その合成から比較射を検出する。
規約：i は単射、j は任意の射。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対的な可逆円柱。 -/
lemma IsPrecompositionEquivalence.pushoutObjObj {A B C D : SSet.{u}}
    {i : A ⟶ B} [Mono i] (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence i) (j : C ⟶ D)
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence sq.ι := by
  have : Mono (i ▷ C) := (tensorRight C).map_mono i
  have hinr := (hi.whiskerRight C).of_isPushout sq.isPushout
  apply hinr.cancel_left
  rw [sq.inr_ι]
  exact hi.whiskerRight D

/-- 概要：第二因子の単射の同値条件も pushout-product に移る。
方針：もう一方の包含を直積の pushout として検出する。
規約：i は任意の射、j は単射。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対的な可逆円柱。 -/
lemma IsPrecompositionEquivalence.pushoutObjObj_right {A B C D : SSet.{u}}
    (i : A ⟶ B) {j : C ⟶ D} [Mono j] (hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence j)
    (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence sq.ι := by
  have : Mono (A ◁ j) := (tensorLeft A).map_mono j
  have hinl := (hj.whiskerLeft A).of_isPushout sq.isPushout.flip
  apply hinl.cancel_left
  rw [sq.inl_ι]
  exact hj.whiskerLeft B

/-- 概要：二つの単射の直積の貼り合わせの比較射は単射。
方針：直積の自然性の四角形が pullback であることと adhesive 性を使う。
規約：前合成の同値条件は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の相対的な可逆円柱の端点の単射性。 -/
lemma mono_pushoutObjObj_ι {A B C D : SSet.{u}} (i : A ⟶ B) (j : C ⟶ D)
    [Mono i] [Mono j] (sq : (curriedTensor SSet.{u}).PushoutObjObj i j) : Mono sq.ι := by
  have : Mono (((curriedTensor SSet.{u}).obj B).map j) := (tensorLeft B).map_mono j
  have : Mono (((curriedTensor SSet.{u}).map i).app D) := (tensorRight D).map_mono i
  refine sq.mono_ι_of_isPullback (IsPullback.mk' (whisker_exchange i j).symm ?_ ?_)
  · intro _ _ _ h₁ h₂
    apply CartesianMonoidalCategory.hom_ext
    · simpa using h₂ =≫ fst _ _
    · simpa using h₁ =≫ snd _ _
  · intro _ a b h
    refine ⟨lift (b ≫ fst _ _) (a ≫ snd _ _), ?_, ?_⟩
    · apply CartesianMonoidalCategory.hom_ext
      · simpa using (h =≫ fst _ _).symm
      · simp
    · apply CartesianMonoidalCategory.hom_ext
      · simp
      · simpa using h =≫ snd _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

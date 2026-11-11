module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedNerveSections

/-!
概要：weighted nerve の切断の族から、底の各射列の初区間の係数を取り出す。
方針：射影の固定条件で底の射列を正規化し、単体的自然性を係数の等式へ移す。
規約：切断は任意のパラメータを持つ底の nerve 上の射として扱う。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断から重み付き自然変換への逆構成。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
variable {I : Type u} [SmallCategory I] {A : SSet.{u}} {H : I ⥤ SSet.{u}}

/-- 概要：切断の族の単体の底の射列は、入力の底の射列そのものである。
方針：射影の固定条件を各次数の入力で評価する。
規約：パラメータは同じ次数の単体。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の係数の型の正規化。 -/
lemma weightedSection_base (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A)
    {n : ℕ} (σ : ComposableArrows I n) (a : A _⦋n⦌) :
    (s.app (Opposite.op ⦋n⦌) (σ, a)).1 = σ := by
  have he := NatTrans.congr_app hs (Opposite.op ⦋n⦌)
  exact congrArg (fun f : (nerve I ⊗ A).obj (Opposite.op ⦋n⦌) ⟶
    (nerve I).obj (Opposite.op ⦋n⦌) => f (σ, a)) he

/-- 概要：切断の族の各単体から、入力の射列上の初区間の係数を取り出す。
方針：射影の条件から得た底の等式で係数の型を移送する。
規約：射列の等式の証明には依存しない。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の逆構成の係数データ。 -/
noncomputable def weightedSectionCoefficients (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A)
    {n : ℕ} (σ : ComposableArrows I n) (a : A _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ σ ⋙ H :=
  (weightedSection_base s hs σ a) ▸ (s.app (Opposite.op ⦋n⦌) (σ, a)).2

/-- 概要：切断の族の単体は底と正規化した係数の組に一致する。
方針：底の等式による移送を依存和の外延性で戻す。
規約：全ての初区間の係数を一度に比較する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の切断の自然性の係数への移送。 -/
lemma weightedSection_app (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A)
    {n : ℕ} (σ : ComposableArrows I n) (a : A _⦋n⦌) :
    s.app (Opposite.op ⦋n⦌) (σ, a) = ⟨σ, weightedSectionCoefficients s hs σ a⟩ := by
  apply Sigma.ext (weightedSection_base s hs σ a)
  dsimp only [weightedSectionCoefficients]
  symm
  apply eqRec_heq_iff.mpr
  rfl

/-- 概要：切断から取り出した係数は任意の単体作用素に沿う制限と可換。
方針：切断の自然性を底と係数の組で書き、底の等式の後に係数を比較する。
規約：パラメータの単体も同じ作用素で制限する。
使われ方：Kerodon 5.3.3.1（Tag 025X）、7.5.3.12（Tag 03B1） の重み付き自然変換の単体的自然性。 -/
lemma weightedSectionCoefficients_restriction (s : nerve I ⊗ A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H)
    (hs : s ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection H = fst (nerve I) A)
    {m n : SimplexCategory} (α : m ⟶ n) (σ : ComposableArrows I n.len)
    (a : A _⦋n.len⦌) :
    weightedSectionCoefficients s hs ((SimplexCategory.toCat.map α).toFunctor ⋙ σ)
        (A.map α.op a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeightRestriction α ≫ Functor.whiskerLeft
        (SimplexCategory.toCat.map α).toFunctor (weightedSectionCoefficients s hs σ a) := by
  have he := congrArg (fun f : (nerve I ⊗ A).obj (Opposite.op n) ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve H).obj (Opposite.op m) => f (σ, a)) (s.naturality α.op)
  change s.app (Opposite.op m) ((SimplexCategory.toCat.map α).toFunctor ⋙ σ,
      A.map α.op a) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveSimplexMap H α (s.app (Opposite.op n) (σ, a)) at he
  rw [weightedSection_app s hs, weightedSection_app s hs] at he
  exact eq_of_heq (Sigma.mk.inj he).2

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

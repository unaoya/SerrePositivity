module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.FiniteSubcomplexColimit
public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Basic.Countable.Basic

/-!
概要：可算な単体集合を有限部分複体の増大列で覆い、単体の最小所属段階を与える。
方針：全単体の符号を有限区間で切り、生成部分複体の有限合併を取る。
規約：有限性は非退化単体についての有限性であり、包含は元の部分複体の包含。
使われ方：有限図式と可算列から余極限を構成する局所左 Kan の段階関手。

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

/-- 概要：各次数が可算なら全単体も可算。
方針：次数とその単体の直和へ埋め込む。
規約：退化単体も数える。使われ方：有限増大列の符号化の入口。 -/
lemma countable_simplices_of_countable_levels (X : SSet.{u})
    [∀ n : ℕ, Countable (X.obj (Opposite.op ⦋n⦌))] : Countable X.S := by
  exact Function.Surjective.countable
    (f := fun s : Σ n, X.obj (Opposite.op ⦋n⦌) ↦ S.mk s.2)
    (fun s ↦ ⟨⟨s.dim, s.simplex⟩, rfl⟩)

/-- 概要：一つの符号に対応する有限生成部分複体。
方針：復号できない符号には空部分複体を割り当てる。
規約：可算性から選んだ符号化を全段階で共有する。
使われ方：有限区間による増大列の構成。 -/
def countableSimplexGenerator (X : SSet.{u}) [Countable X.S] (i : ℕ) : X.Subcomplex :=
  letI := Encodable.ofCountable X.S
  (Encodable.decode (α := X.S) i).elim ⊥ S.subcomplex

/-- 概要：各符号の生成部分複体は有限。
方針：空部分複体または一単体の生成部分複体の有限性を使う。
規約：符号が実在するかどうかを仮定しない。使われ方：各段階の有限性。 -/
instance countableSimplexGenerator_finite (X : SSet.{u}) [Countable X.S] (i : ℕ) :
    SSet.Finite (countableSimplexGenerator X i) := by
  let := Encodable.ofCountable X.S
  unfold countableSimplexGenerator
  cases Encodable.decode (α := X.S) i with
  | none => exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.finite_subcomplex_bot X
  | some s => exact inferInstanceAs (SSet.Finite (Subcomplex.ofSimplex s.simplex))

/-- 概要：最初の n 個の符号が生成する有限部分複体。
方針：Fin n を添字として生成部分複体を合併する。
規約：第零段階は空部分複体。使われ方：可算形状の有限増大列。 -/
def countableFiniteStage (X : SSet.{u}) [Countable X.S] (n : ℕ) : X.Subcomplex :=
  ⨆ i : Fin n, countableSimplexGenerator X i.val

/-- 概要：増大列の各段階は有限。
方針：有限個の有限部分複体の合併の有限性を使う。
規約：単体集合としての有限性を公開する。使われ方：全有限図式への仮定の適用。 -/
instance countableFiniteStage_finite (X : SSet.{u}) [Countable X.S] (n : ℕ) :
    SSet.Finite (countableFiniteStage X n) :=
  (SSet.finite_iSup_iff (fun i : Fin n ↦ countableSimplexGenerator X i.val)).2
    (fun _ ↦ inferInstance)

/-- 概要：有限段階は単調に増大する。
方針：Fin n の符号を同じ値の Fin m の符号へ送る。
規約：部分複体の包含を結論する。使われ方：可算列の射と所属段階の比較。 -/
lemma countableFiniteStage_monotone (X : SSet.{u}) [Countable X.S] :
    Monotone (countableFiniteStage X) := by
  intro n m h
  refine iSup_le fun i ↦ ?_
  exact le_iSup_of_le (⟨i.val, lt_of_lt_of_le i.isLt h⟩ : Fin m) le_rfl

/-- 概要：各単体はある有限段階に含まれる。
方針：単体の符号の次の段階を選び、符号化の復号則を使う。
規約：生成部分複体全体の包含を結論する。使われ方：最小所属段階の定義。 -/
lemma exists_countableFiniteStage (X : SSet.{u}) [Countable X.S] (s : X.S) :
    ∃ n, s.subcomplex ≤ countableFiniteStage X n := by
  let := Encodable.ofCountable X.S
  refine ⟨Encodable.encode s + 1, ?_⟩
  have h : s.subcomplex = countableSimplexGenerator X (Encodable.encode s) := by
    simp [countableSimplexGenerator, Encodable.encodek]
  rw [h]
  exact le_iSup (fun i : Fin (Encodable.encode s + 1) ↦ countableSimplexGenerator X i.val)
    ⟨Encodable.encode s, Nat.lt_succ_self _⟩

/-- 概要：有限増大列は元の単体集合全体を覆う。
方針：各単体の生成部分複体が一段階に含まれることを使う。
規約：部分複体の上限を元の全体と同定する。使われ方：増大列の余極限の同定。 -/
lemma iSup_countableFiniteStage (X : SSet.{u}) [Countable X.S] :
    (⨆ n, countableFiniteStage X n) = ⊤ := by
  apply top_unique
  intro n x _
  obtain ⟨⟨n⟩⟩ := n
  obtain ⟨i, hi⟩ := exists_countableFiniteStage X (S.mk x)
  exact (le_iSup (countableFiniteStage X) i) _ (hi _ (Subcomplex.mem_ofSimplex_obj x))

/-- 概要：単体の最小所属段階。
方針：生成部分複体を含む段階の最小値を選ぶ。
規約：所属は頂点だけでなく単体全体で判定する。
使われ方：反対 transport 単体圏から可算順序圏への関手。 -/
def countableSimplexStage (X : SSet.{u}) [Countable X.S] (s : X.S) : ℕ := by
  classical
  exact Nat.find (exists_countableFiniteStage X s)

/-- 概要：最小所属段階は段階への所属を正確に判定する。
方針：最小性と有限段階の単調性を両方向に使う。
規約：等号でなく包含で判定する。使われ方：段階関手のコンマ圏の同定。 -/
lemma countableSimplexStage_le_iff (X : SSet.{u}) [Countable X.S] (s : X.S) (n : ℕ) :
    countableSimplexStage X s ≤ n ↔ s.subcomplex ≤ countableFiniteStage X n := by
  classical
  constructor
  · intro h
    exact (Nat.find_spec (exists_countableFiniteStage X s)).trans
      (countableFiniteStage_monotone X h)
  · exact Nat.find_min' (exists_countableFiniteStage X s)

/-- 概要：面と退化を取ると最小所属段階は増えない。
方針：生成部分複体の包含と最小所属段階の判定を合成する。
規約：単体の前順序に関する単調性。使われ方：段階関手の射の定義。 -/
lemma countableSimplexStage_monotone (X : SSet.{u}) [Countable X.S] :
    Monotone (countableSimplexStage X) := by
  intro s t h
  apply (countableSimplexStage_le_iff X s _).2
  exact (show s.subcomplex ≤ t.subcomplex from h).trans
    ((countableSimplexStage_le_iff X t _).1 le_rfl)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

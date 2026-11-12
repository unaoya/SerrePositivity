module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.SetTheory.Cardinal.HasCardinalLT
public import Mathlib.Data.Fintype.Option

/-!
概要：非退化単体数と各次数の単体数を、正則非可算濃度の下で比較する。
方針：非退化表示による全射と可算直和を使い、有限源の関数族は有限積で評価する。
規約：F2 の小ささ述語を複製せず、宇宙多相な HasCardinalLT で述べる。
使われ方：Ind-S (7)、内ホーン充填閉包の濃度評価。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 概要：非可算濃度には自然数全体も収まる。
方針：濃度の宇宙持ち上げを簡約する。規約：正則性は不要。
使われ方：段階と次元の可算和の添字評価。 -/
lemma hasCardinalLT_nat {μ : Cardinal.{u}} (hω : Cardinal.aleph0 < μ) :
    HasCardinalLT ℕ μ := by
  simpa [HasCardinalLT] using hω

/-- 概要：有限個の選択を持つ関数族は同じ無限濃度未満。
方針：有限集合を空集合と Option で帰納し、関数を値と残りの関数へ単射に送る。
規約：強極限性・正則性は不要。使われ方：有限個のホーン面の値の評価。 -/
lemma hasCardinalLT_finite_arrow {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    {T : Type v} (hT : HasCardinalLT T μ) (I : Type w) [Finite I] :
    HasCardinalLT (I → T) μ := by
  induction I using Finite.induction_empty_option with
  | of_equiv e ih =>
    exact (hasCardinalLT_iff_of_equiv (Equiv.arrowCongr e (Equiv.refl T)) μ).mp ih
  | h_empty => exact hasCardinalLT_of_finite _ μ hμ
  | @h_option I _ ih =>
    apply (hasCardinalLT_prod hμ hT ih).of_injective
      (fun f : Option I → T => (f none, fun i => f (some i)))
    intro f g h
    funext i
    cases i with
    | none => exact congrArg Prod.fst h
    | some i => exact congrFun (congrArg Prod.snd h) i

/-- 概要：非退化単体数が小さければ全ての次数の単体数も小さい。
方針：非退化単体と有限な単体圏射の対から各単体へ全射を作る。
規約：退化表示の一意性は使わない。使われ方：充填を追加する前の面の個数の評価。 -/
lemma hasCardinalLT_obj_of_N {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (X : SSet.{v}) (hX : HasCardinalLT X.N μ) (n : ℕ) :
    HasCardinalLT (X _⦋n⦌) μ := by
  letI : Fact μ.IsRegular := ⟨hμ⟩
  have h := hasCardinalLT_sigma (fun s : X.N => (⦋n⦌ ⟶ ⦋s.dim⦌)) μ hX
    (fun _ => hasCardinalLT_of_finite _ μ hμ.aleph0_le)
  apply h.of_surjective (fun z => X.map z.2.op z.1.simplex)
  intro x
  obtain ⟨m, f, _, y, hy⟩ := X.exists_nonDegenerate x
  exact ⟨⟨N.mk y.val y.property, f⟩, hy.symm⟩

/-- 概要：全次数が小さければ、非退化単体の全族も同じ非可算正則濃度未満。
方針：次元と元の単体の対への単射を可算直和で評価する。
規約：各次数の有限性は不要。使われ方：閉包の次数別評価を要求する濃度評価へ戻す。 -/
lemma hasCardinalLT_N_of_obj {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    (hω : Cardinal.aleph0 < μ) (X : SSet.{v})
    (hX : ∀ n : ℕ, HasCardinalLT (X _⦋n⦌) μ) : HasCardinalLT X.N μ := by
  letI : Fact μ.IsRegular := ⟨hμ⟩
  have h := hasCardinalLT_sigma (fun n : ℕ => X _⦋n⦌) μ (hasCardinalLT_nat hω) hX
  apply h.of_injective (fun s : X.N => (⟨s.dim, s.simplex⟩ : Σ n : ℕ, X _⦋n⦌))
  intro a b hab
  obtain ⟨n, ⟨x, hx⟩, rfl⟩ := a.mk_surjective
  obtain ⟨m, ⟨y, hy⟩, rfl⟩ := b.mk_surjective
  change (⟨n, x⟩ : Σ n : ℕ, X _⦋n⦌) = ⟨m, y⟩ at hab
  cases hab
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

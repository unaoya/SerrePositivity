module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseStandardSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.Projection
public import Mathlib.SetTheory.Cardinal.HasCardinalLT

/-!
概要：非可算正則 κ に対し κ-small な形状の全単体族と twisted arrow も κ-small。
方針：非退化単体からの退化表示を有限な添字で数え、全次数の可算和を評価する。
規約：非退化単体だけの条件から退化単体を含む全体の評価を導く。
使われ方：P-12、関手圏の写像空間を計算する小さい end の形状。

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

/-- 概要：κ-small な単体集合の各次数の全単体も κ 個未満。
方針：非退化単体とそれからの有限な退化写像で全単体を被覆する。
規約：κ は正則無限、退化の次元の一様上界は要求しない。
使われ方：end の形状の全単体の濃度評価。 -/
lemma hasCardinalLT_simplex_of_isKappaSmall {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) (n : ℕ) : HasCardinalLT (K _⦋n⦌) κ := by
  have hκ : κ.IsRegular := Fact.out
  have hN : HasCardinalLT K.N κ := (hasCardinalLT_iff_cardinal_mk_lt _ _).mpr hK
  let A (s : K.N) := ULift.{u} (⦋n⦌ ⟶ ⦋s.dim⦌)
  have hA : HasCardinalLT (Σ s : K.N, A s) κ :=
    hasCardinalLT_sigma A κ hN (fun s ↦ hasCardinalLT_of_finite _ _ hκ.aleph0_le)
  apply hA.of_surjective (fun a ↦ K.map a.2.down.op a.1.simplex)
  intro x
  obtain ⟨m, f, _, y, hy⟩ := K.exists_nonDegenerate x
  exact ⟨⟨SSet.N.mk y.val y.property, ULift.up f⟩, hy.symm⟩

/-- 概要：各次数が κ 未満なら非可算正則 κ に対し全次数の単体族も κ 未満。
方針：次数を持ち上げた自然数で添字付け、正則性による和の評価を使う。
規約：全ての退化単体も数える。
使われ方：twisted arrow や全単体添字の小ささ。 -/
lemma hasCardinalLT_allSimplices {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) {K : SSet.{u}}
    (hK : ∀ n, HasCardinalLT (K _⦋n⦌) κ) :
    HasCardinalLT (Σ n : ULift.{u} ℕ, K _⦋n.down⦌) κ := by
  have hNat : HasCardinalLT (ULift.{u} ℕ) κ := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    simpa only [Cardinal.mk_uLift, Cardinal.mk_nat, Cardinal.lift_aleph0] using hκ
  exact hasCardinalLT_sigma _ κ hNat (fun n ↦ hK n.down)

/-- 概要：κ-small な形状の twisted arrow も同じ κ-small。
方針：twisted arrow の各次数を元の二倍次数の単体へ埋め込み、可算和を数える。
規約：κ は非可算正則、元の形状の quasicategory 性は不要。
使われ方：関手圏の end と κ-filtered 余極限の交換。 -/
lemma isKappaSmall_twistedArrow {κ : Cardinal.{u}} [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 < κ) {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow K) := by
  have hEach (n : ℕ) : HasCardinalLT ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow K) _⦋n⦌) κ :=
    (hasCardinalLT_simplex_of_isKappaSmall hK (n + n + 1)).of_injective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSimplexEquiv K n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSimplexEquiv K n).injective
  have hAll := hasCardinalLT_allSimplices hκ hEach
  have hN : HasCardinalLT (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow K).N κ := hAll.of_injective
    (fun s ↦ ⟨ULift.up s.dim, s.simplex⟩) (by
      rintro ⟨⟨n, s⟩, hs⟩ ⟨⟨m, t⟩, ht⟩ he
      cases he
      rfl)
  exact (hasCardinalLT_iff_cardinal_mk_lt _ _).mp hN

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

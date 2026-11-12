module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCandidateFamily
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ObjectCompactCardinals

/-!
概要：引き戻し候補の両成分と標的像に共通する compact 濃度を構成する。
方針：三つの accessible 圏で小さい族の濃度を順に揃え、最後に濃度変更条件を満たす。
規約：引き戻し自身の accessibility や compact 性は入力にしない。
使われ方：候補の写像空間の引き戻しと filtered 余極限の交換。

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

/-- 概要：小さい二対象族と両標的像を一つの正則濃度で compact にする。
方針：各族の共通濃度を取り、compact 性の単調性で最後の濃度へ移す。
規約：指定した下限 κ に対する明示的な濃度変更条件も保持する。
使われ方：引き戻し候補の同時 compact 濃度。 -/
lemma exists_pullbackFamily_compactCardinal
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible D) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible B)
    {AE AD : Type u} (vE : AE → E _⦋0⦌) (vD : AD → D _⦋0⦌)
    (κ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ ∧
      (∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (vE a)) ∧
      (∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (vD d)) ∧
      (∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ (vE a))) ∧
      (∀ d, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ (vD d))) := by
  obtain ⟨ρE, _, _, hcE⟩ := hE.exists_common_compactCardinal vE κ
  obtain ⟨ρD, _, hED, hcD⟩ := hD.exists_common_compactCardinal vD ρE
  let vB : AE ⊕ AD → B _⦋0⦌ := Sum.elim
    (fun a ↦ p.app _ (vE a)) (fun d ↦ q.app _ (vD d))
  obtain ⟨ρB, _, hDB, hcB⟩ := hB.exists_common_compactCardinal vB ρD
  obtain ⟨μ, hμ, hBμ, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_cardinalChangeBound κ ρB
  have hDμ : ρD ≤ μ := hDB.le.trans hBμ.le
  have hEμ : ρE ≤ μ := hED.le.trans hDμ
  refine ⟨μ, hμ, hb, fun a ↦ (hcE a).of_le hEμ,
    fun d ↦ (hcD d).of_le hDμ, ?_, ?_⟩
  · exact fun a ↦ (hcB (Sum.inl a)).of_le hBμ.le
  · exact fun d ↦ (hcB (Sum.inr d)).of_le hBμ.le

/-- 概要：元の引き戻し候補の両成分と共通の標的像は同じ濃度で compact。
方針：小さい元の族とその像の濃度を揃え、候補の第一成分の同型で移す。
規約：標的の局所小ささは accessibility から得て、追加の存在入力を残さない。
使われ方：候補の写像空間を成分と底の写像空間から計算する交換の入力。 -/
lemma exists_pullbackCandidate_compactCardinal
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible D) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible B)
    {AE AD : Type u} (vE : AE → E _⦋0⦌) (vD : AD → D _⦋0⦌)
    (κ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ ∧
      ∀ t : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PullbackCandidateIndex p q hB.isLocallySmall vE vD,
      let z := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCandidateFamily p q hB.isLocallySmall vE vD hp t
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((pullback.fst p q).app _ z) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((pullback.snd p q).app _ z) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ ((pullback.fst p q).app _ z)) := by
  obtain ⟨μ, hμ, hb, hvE, hvD, hvBE, _⟩ :=
    exists_pullbackFamily_compactCardinal p q hE hD hB vE vD κ
  refine ⟨μ, hμ, hb, fun t ↦ ?_⟩
  obtain ⟨he, hd⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCandidateFamily_components_compact
    p q hB.isLocallySmall vE vD hp hvE hvD t
  refine ⟨he, hd, ?_⟩
  let e := (hoFunctor.map p).toFunctor.mapIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pullbackCandidateFamily_fstIso p q hB.isLocallySmall vE vD hp t)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_iff_of_iso e).mpr (hvBE t.1)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

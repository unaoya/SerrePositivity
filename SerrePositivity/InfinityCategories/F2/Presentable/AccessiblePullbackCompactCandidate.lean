module

public import SerrePositivity.InfinityCategories.F2.Presentable.ComponentCompactGeneralModels
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleSpanCompactCardinals
public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackFilteredColimits

/-!
概要：accessible cospan の元の引き戻し内に小さい native compact 全部分候補圏を構成する。
方針：両関手の共通 compact 保存濃度と、compact 成分の小さい模型を合わせる。
規約：filtered 生成性と引き戻しの presentable 性はこの段階で結論しない。
使われ方：引き戻しの各対象の filtered 表示を接続する生成候補。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の accessible cospan の引き戻しに、compact 成分の全対象を代表する小さい compact 全部分圏がある。
方針：共通濃度での compact 成分圏の小さい全同値模型を、元の引き戻しへ包含する。
規約：同じ元の引き戻し内の compact 性を供給し、濃度の下限 σ を保持する。
使われ方：filtered 生成性を証明すれば accessibility へ直接接続できる候補。 -/
lemma exists_accessiblePullback_compactCandidate
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : IsAccessible E) (hD : IsAccessible D) (hB : IsAccessible B)
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (hpc : IsAccessibleFunctor p) (hqc : IsAccessibleFunctor q) (σ : Cardinal.{u}) :
    letI := hp.innerFibration
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ pullback p q,
          IsFullyFaithful i ∧
          (∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} μ (i.app _ (ULift.up a))) ∧
          (∀ a : A _⦋0⦌, ComponentCompactVertex μ p q (i.app _ (ULift.up a))) ∧
          ∀ x, ComponentCompactVertex μ p q x →
            ∃ a : A _⦋0⦌, Nonempty (VertexIso x (i.app _ (ULift.up a))) := by
  have : InnerFibration p := hp.innerFibration
  obtain ⟨κ, μ, hκ, hμ, hσ, hκμ, he, hd, hb, hpμ, hqμ, hpCompact, hqCompact⟩ :=
    exists_accessibleSpan_compactCardinal hE hD hB p q hpc hqc σ
  have : Fact κ.IsRegular := ⟨hκ⟩
  have : Fact μ.IsRegular := ⟨hμ⟩
  obtain ⟨A, hA, ⟨a⟩⟩ := exists_smallComponentCompactModel he hd hb p q hp hpCompact hqCompact
  have := hA
  let j := (fullSubcomplexOnVertices (pullback p q) (ComponentCompactVertex μ p q)).ι
  let i := a.hom ≫ j
  have hf := pullback_fst_isKappaAccessibleFunctor p q hp
    he.hasSmallKappaFilteredColimits hd.hasSmallKappaFilteredColimits hpμ hqμ
  have hs := pullback_snd_isKappaAccessibleFunctor p q hp
    he.hasSmallKappaFilteredColimits hd.hasSmallKappaFilteredColimits hpμ hqμ
  refine ⟨μ, hμ, hσ, A, hA, i,
    a.isQCatEquivalence.isFullyFaithful.comp
      (isFullyFaithful_fullSubcomplexOnVertices_ι _ _), ?_, ?_, ?_⟩
  · intro x
    exact componentCompactObjects_vertex_isKappaCompact μ p q hκμ hf hs
      hpμ hpCompact (a.hom.app _ (ULift.up x))
  · intro x
    exact fullSubcomplexOnVertices_vertex (a.hom.app _ (ULift.up x))
  · intro x hx
    let xx : (componentCompactObjects μ p q) _⦋0⦌ := ⟨x, by
      intro α
      have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      subst α
      simpa only [op_id, CategoryTheory.Functor.map_id_apply] using hx⟩
    refine ⟨(a.inv.app _ xx).down, ⟨?_⟩⟩
    exact ((a.invHomIso.app xx).map j).symm

end SerrePositivity.InfinityCategories.F2.Presentable

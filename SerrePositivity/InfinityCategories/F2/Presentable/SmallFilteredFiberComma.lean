module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactSourcePullbackModels
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFiberTestCocones
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallTestFilteredModels
public import SerrePositivity.InfinityCategories.F2.Presentable.PointAccessibility

/-!
概要：点 fiber の compact comma に小さい同じ濃度の filtered 全模型を与える。
方針：成分 slice の小模型を貼り、全 μ-small 試験余錐を同値の逆で戻す。
規約：元の対象を保ち、生成性や accessibility 自体はここでは結論しない。
使われ方：元の fiber の compact 生成表示の添字。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：点射の指定標的が μ-compact なら点射は全頂点の μ-compact 性を保つ。
方針：点への二つの点射の唯一性で像を元の標的頂点と同定する。
規約：μ の正則性や余極限保存は要求しない。
使われ方：compact 成分 slice の小模型への点射の入力。 -/
lemma pointMap_preservesKappaCompact {μ : Cardinal.{u}}
    {B : SSet.{u + 1}} [Quasicategory B]
    (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hq : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv q))
    (d : (Δ[0] : SSet.{u + 1}) _⦋0⦌) :
    Compact.IsKappaCompact.{u, u + 1} μ (q.app _ d) := by
  have hd : SSet.yonedaEquiv.symm d = 𝟙 (Δ[0] : SSet.{u + 1}) :=
    SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  have hqd : q.app _ d = SSet.yonedaEquiv q := by
    calc
      q.app _ d = SSet.yonedaEquiv (SSet.yonedaEquiv.symm d ≫ q) := by
        rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
      _ = SSet.yonedaEquiv q := by rw [hd, Category.id_comp]
  rw [hqd]
  exact hq

/-- 概要：点 fiber の compact comma は小さい μ-filtered 全模型を持つ。
方針：compact 始域 slice の小模型と任意 μ-small 全試験余錐を合成する。
規約：点射には固定標的の compact 性のみを要求し、全小余極限保存を要求しない。
使われ方：元の fiber の生成表示へ接続する小さい添字。 -/
lemma exists_smallKappaFilteredFiberCommaModel
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits B)
    (hEμ : IsKappaAccessible μ E) (hBμ : IsKappaAccessible μ B)
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hp : F1B.EquivalenceLifting p) (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p)
    (hpCompact : ∀ e, Compact.IsKappaCompact.{u, u + 1} μ e →
      Compact.IsKappaCompact.{u, u + 1} μ (p.app _ e))
    (hq : Compact.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv q))
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q) :
    letI := hp.innerFibration
    ∃ (M : SSet.{u}) (hM : Quasicategory M), letI := hM
      IsKappaFiltered μ M ∧ Nonempty
        (QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj M) (componentCompactOver μ p q x)) := by
  have : InnerFibration p := hp.innerFibration
  obtain ⟨M, hM, ⟨e⟩⟩ := exists_smallComponentCompactOverModel p q hp hEμ
    (point_isKappaAccessible μ Fact.out) hBμ hpCompact
    (fun d _ ↦ pointMap_preservesKappaCompact q hq d) x
  have := hM
  have hfiltered : IsKappaFiltered μ M :=
    isKappaFiltered_of_small_tests_equivalence e (fun K hK r ↦
      nonempty_componentCompactFiberOver_cocone_of_small hμ K hK hE hB hEμ
        p q hp hpc hpCompact hq x r)
  exact ⟨M, hM, hfiltered, ⟨e⟩⟩

end SerrePositivity.InfinityCategories.F2.Presentable

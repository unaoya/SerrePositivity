module

public import SerrePositivity.InfinityCategories.F2.Presentable.ComponentCompactOverSmallTests
public import SerrePositivity.InfinityCategories.Core.UniverseLimits
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeExistenceTransport

/-!
概要：小さい全試験形状への余錐を、指定された小さい全同値模型の filtered 性へ移す。
方針：同値の逆で余錐を戻し、全関手同型と宇宙持ち上げの全射性で戻す。
規約：小さい模型の存在は別途構成し、ここでは指定模型そのものを扱う。
使われ方：compact comma の小さい生成添字を κ-filtered にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：全小試験形状への余錐を持つ圏の小さい全同値模型は κ-filtered。
方針：元の同値で余錐を送って戻し、同じ全図式へ厳密化する。
規約：元の κ を保ち、同型を点ごとに選び直さない。
使われ方：大きい compact comma の小さい模型の filtered 性。 -/
lemma isKappaFiltered_of_small_tests_equivalence {κ : Cardinal.{u}}
    {M : SSet.{u}} [Quasicategory M] {C : SSet.{u + 1}} [Quasicategory C]
    (e : QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj M) C)
    (hC : ∀ (K : SSet.{u}), IsKappaSmall κ K →
      ∀ r : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C, Nonempty (JoinCocone r)) :
    IsKappaFiltered κ M := by
  constructor
  intro K hK f
  let F := (SSet.uliftFunctor.{u + 1, u}).map f
  obtain ⟨c⟩ := hC K hK (F ≫ e.hom)
  have hc : Nonempty (JoinCocone (F ≫ (e.hom ≫ e.inv))) :=
    ⟨⟨c.val ≫ e.inv, by rw [← Category.assoc, c.property, Category.assoc]⟩⟩
  have he : FunctorIso (F ≫ (e.hom ≫ e.inv)) F := by
    simpa only [Category.comp_id] using FunctorIso.precomp e.homInvIso F
  obtain ⟨d⟩ := nonempty_joinCocone_of_functorIso he hc
  obtain ⟨d₀, _⟩ := JoinCocone.ulift_surjective.{u, u + 1} f d
  exact ⟨d₀⟩

/-- 概要：compact 成分の対象上の comma の小さい模型は同じ μ-filtered 添字になる。
方針：全 μ-small 試験形状の内部余錐を同値で小さい模型へ戻す。
規約：指定した小模型の存在や生成性を結論に隠さない。
使われ方：元の対象の filtered 生成表示の添字。 -/
lemma componentCompactOver_model_isKappaFiltered
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (hE : HasSmallColimits E) (hD : HasSmallColimits D)
    (hpc : PreservesSmallColimits p) (hqc : PreservesSmallColimits q)
    (x : (Δ[0] : SSet.{u + 1}) ⟶ pullback p q)
    {M : SSet.{u}} [Quasicategory M]
    (e : letI := hp.innerFibration
      QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj M)
      (componentCompactOver μ p q x)) : IsKappaFiltered μ M := by
  have : InnerFibration p := hp.innerFibration
  exact isKappaFiltered_of_small_tests_equivalence e (fun K hK r ↦
    nonempty_componentCompactOver_cocone_of_small hμ K hK p q hp hE hD hpc hqc x r)

end SerrePositivity.InfinityCategories.F2.Presentable

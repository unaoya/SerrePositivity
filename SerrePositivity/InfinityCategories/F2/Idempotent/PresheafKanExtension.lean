module

public import SerrePositivity.InfinityCategories.F2.Idempotent.PresheafLocalKanColimits
public import SerrePositivity.InfinityCategories.F2.Idempotent.UniverseFullyFaithful
public import SerrePositivity.InfinityCategories.F1.Universe.InnerFibration
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftStrictExistence

/-!
概要：持ち上げた元の全部分圏包含に沿って、任意の元の前層図式を厳密に延長する。
方針：元の全局所余極限の存在と、持ち上げた元の包含の性質を厳密な左 Kan 存在へ渡す。
規約：元の図式を制限の等式で回収する。前層圏の大きい余極限を入力に仮定しない。
使われ方：HTT 5.1.4.8 の元の Yoneda 後合成の延長。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 持ち上げた元の全部分圏包含に沿って、前層図式を厳密に回収する左 Kan 関手が存在。 -/
lemma exists_presheafKan_strict_extension {K C E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (δ : K ⟶ C) [Mono δ] [InnerFibration δ]
    (hδ : IsFullyFaithful δ)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ PresheafInfinity E) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ PresheafInfinity E,
      (SSet.uliftFunctor.{u + 1, u}).map δ ≫ G = F₀ ∧
      ∀ c, IsColimitCone
        (leftKanCanonicalCocone ((SSet.uliftFunctor.{u + 1, u}).map δ) G c) := by
  have : Mono ((SSet.uliftFunctor.{u + 1, u}).map δ) := idemUliftMap_mono δ
  exact F1B.exists_kanLeftCanonical_strict_extension_of_local_colimits
    ((SSet.uliftFunctor.{u + 1, u}).map δ) (IsFullyFaithful.ulift hδ) F₀
    (presheafLocalKanDiagram_hasColimit δ F₀)

end SerrePositivity.InfinityCategories.F2.Idempotent

module

public import SerrePositivity.InfinityCategories.F2.Ind.FinitePosetCoherentExchange
public import SerrePositivity.InfinityCategories.F2.Presentable.PullbackExchangeShape
public import SerrePositivity.InfinityCategories.F1.Simplicial.FiniteCospanNerveIso

/-!
概要：有限 poset の交換から、cospan・標準単体・空形状の交換を得る。
方針：ℵ₀-filtered 性の同値と、全錐を保つ形状同型による移送を使う。
規約：元の coherent 全族と指定余錐を保持する。
使われ方：I-2 d′ の全有限形状への pushout 帰納の基底。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open Presentable

/-- ℵ₀ の cardinal 版と通常の coherent filtered 交換は同じ全錐を量化する。 -/
lemma coherentFilteredLimitExchangeShape_iff_cardinal_aleph0 (K : SSet.{u}) :
    CoherentFilteredLimitExchangeShape K ↔
      CardinalFilteredLimitExchangeShape Cardinal.aleph0.{u} K := by
  constructor
  · intro h B hB hFiltered F c hc hF
    have : IsFilteredInfinity B := (isKappaFiltered_aleph0_iff B).mp hFiltered
    exact h B F c hc hF
  · intro h B hB hFiltered F c hc hF
    have : IsKappaFiltered Cardinal.aleph0.{u} B :=
      (isKappaFiltered_aleph0_iff B).mpr hFiltered
    exact h B F c hc hF

/-- 同じ全錐の交換は形状の厳密な同型で移る。 -/
lemma coherentFilteredLimitExchangeShape_of_iso {A B : SSet.{u}} (e : A ≅ B)
    (h : CoherentFilteredLimitExchangeShape A) : CoherentFilteredLimitExchangeShape B :=
  (coherentFilteredLimitExchangeShape_iff_cardinal_aleph0 B).mpr
    (((coherentFilteredLimitExchangeShape_iff_cardinal_aleph0 A).mp h).of_iso e)

/-- 元の通常 cospan の全錐は、一般 coherent filtered 余極限で極限性を保つ。 -/
lemma coherentFilteredLimitExchangeShape_cospan :
    CoherentFilteredLimitExchangeShape (nerve (AsSmall.{u} WalkingCospan)) :=
  coherentFilteredLimitExchangeShape_of_iso pullbackExchangeNerveIso
    (coherentFilteredLimitExchangeShape_finite_poset PullbackExchangeIndex.{u})

/-- 元の cospan ホーンの全錐交換。 -/
lemma coherentFilteredLimitExchangeShape_cospanHorn :
    CoherentFilteredLimitExchangeShape (horn 2 2 : SSet.{u}) :=
  coherentFilteredLimitExchangeShape_of_iso finiteCospanNerveIso
    (coherentFilteredLimitExchangeShape_finite_poset FiniteCospanIndex.{u})

/-- 元の全標準単体について全錐交換が成立する。 -/
lemma coherentFilteredLimitExchangeShape_simplex (n : ℕ) :
    CoherentFilteredLimitExchangeShape (Δ[n] : SSet.{u}) :=
  coherentFilteredLimitExchangeShape_of_iso (stdSimplex.isoNerve n).symm
    (coherentFilteredLimitExchangeShape_finite_poset (ULift.{u} (Fin (n + 1))))

/-- 空部分複体上の元の全錐交換。 -/
lemma coherentFilteredLimitExchangeShape_empty (X : SSet.{u}) :
    CoherentFilteredLimitExchangeShape (⊥ : X.Subcomplex) := by
  have he : nerve (ULift.{u} (Fin 0)) ≅ (⊥ : X.Subcomplex) := by
    refine NatIso.ofComponents (fun n ↦ ?_) ?_
    · have : IsEmpty ((nerve (ULift.{u} (Fin 0))).obj n) := ⟨fun s ↦ (s.obj 0).down.elim0⟩
      have : IsEmpty (((⊥ : X.Subcomplex) : SSet.{u}).obj n) := ⟨fun s ↦ s.property⟩
      exact Equiv.toIso (Equiv.equivOfIsEmpty _ _)
    · intro n m f
      ext s
      exact (s.obj 0).down.elim0
  exact coherentFilteredLimitExchangeShape_of_iso he
    (coherentFilteredLimitExchangeShape_finite_poset (ULift.{u} (Fin 0)))

end SerrePositivity.InfinityCategories.F2.Ind

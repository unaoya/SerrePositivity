module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallLimitFamilyPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.KappaFilteredUniverse
public import SerrePositivity.InfinityCategories.F2.Compact.HomConeFamily
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices

/-!
概要：μ-small な小さい ∞ 圏を添字とする μ-compact 頂点の余極限は μ-compact。
方針：元の全 Hom 極限錐族を、同じ μ で連続な極限関手と全自然に比較する。
規約：μ は非可算正則で、添字と標的の宇宙を分離する。
使われ方：引き戻しの小さい compact 候補の余極限閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open Compact

/-- 概要：反対単体集合への移行は非退化単体による小ささを保存・反映する。
方針：非退化単体の反転全単射で濃度を比較する。
規約：正則性を要求しない。
使われ方：余極限の Hom 極限錐の反対形状。 -/
lemma isKappaSmall_op_iff {μ : Cardinal.{u}} (K : SSet.{u}) :
    IsKappaSmall μ K.op ↔ IsKappaSmall μ K := by
  unfold IsKappaSmall
  rw [Cardinal.mk_congr (SSet.N.opEquiv (X := K)).toEquiv]

/-- 概要：μ-small な quasicategory 形状の μ-compact 頂点の余極限は μ-compact。
方針：元の余極限からの全 Hom 錐族に、同じ μ の小極限関手の連続性を適用する。
規約：一般の有限交換入力や大きい宇宙の compact 性を追加入力にしない。
使われ方：元の引き戻しの compact 候補圏の小さい余極限閉性。 -/
lemma isKappaCompact_smallQuasicategoryColimit_universe
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    (K : SSet.{u}) [Quasicategory K] (hK : IsKappaSmall μ K)
    {C : SSet.{max u v}} [Quasicategory C]
    {D : (SSet.uliftFunctor.{v, u}).obj K ⟶ C}
    (c : JoinCocone D) (hc : IsColimitCone c)
    (hD : ∀ k : ((SSet.uliftFunctor.{v, u}).obj K) _⦋0⦌,
      IsKappaCompact.{u, v} μ (D.app (Opposite.op ⦋0⦌) k)) :
    IsKappaCompact.{u, v} μ c.vertex := by
  have hK' : IsKappaSmall (Cardinal.lift.{v} μ)
      (((SSet.uliftFunctor.{v, u}).obj K).op) :=
    (isKappaSmall_op_iff _).mpr ((isKappaSmall_ulift_iff μ K).mpr hK)
  have h := preservesKappaFilteredColimits_limitFamily_apex_of_small hμ hK'
    (colimitRepresentableFamily c)
    (by rintro ⟨y⟩; exact colimitRepresentableFamily_isLimit c hc y)
    (by
      rintro ⟨k⟩
      obtain ⟨k, rfl⟩ := SSet.opObjEquiv.symm.surjective k
      rw [colimitRepresentableFamily_right]
      exact hD k)
  rw [colimitRepresentableFamily_apex] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Presentable

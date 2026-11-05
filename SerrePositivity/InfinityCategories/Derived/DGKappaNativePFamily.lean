module
public import SerrePositivity.InfinityCategories.Derived.DGKappaNativeMoritaFamily

/-!
概要：元の実評価 Morita 全族から、指定 P/Yoneda 比較の全族を追加入力なしで作る。
方針：実構成した Morita 全族を21:25の相対延長へ代入し、元の全比較を厳密回収する。
規約：固定源 S 内の核作用との照合と、元の導来模型の P.inclusion の全族は別工程。
懸垂作用や全四角形の存在をこの結果で完成扱いしない。I・P・ν・K は変更しない。
使われ方：D-8 e の実 Morita／P/Yoneda 全入力比較の供給部品。
-/
@[expose] public noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.KST.SConstruction SerrePositivity.KST.NonConnective
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] {κ : Cardinal.{u}}
  (s : DGSuspensionStageProvider.{u, v} R κ)

/-- 同じ実 Morita 全族から構成した、元の P/Yoneda 比較の全入力族。 -/
def dgKappaNativePComparisonFamily : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    equivalencePath ((ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj
      _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{max (u + 1) v}) :=
  (dgKappaNativePFamily_exists R s (dgKappaNativeMoritaArrowFamily R s)
    (dgKappaNativeMoritaArrowFamily_at R s)).choose

lemma dgKappaNativePComparisonFamily_boundary :
    dgKappaNativePComparisonFamily R s ≫
        equivalencePathMap ((pre (boundary 1).ι).app _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{max (u + 1) v}) =
      (dgKappaNativeMoritaArrowFamily R s ≫ (pre (boundary 1).ι).app _) ≫
        equivalencePathRefl _ :=
  (dgKappaNativePFamily_exists R s (dgKappaNativeMoritaArrowFamily R s)
    (dgKappaNativeMoritaArrowFamily_at R s)).choose_spec.1

lemma dgKappaNativePComparisonFamily_one :
    dgKappaNativePComparisonFamily R s ≫ equivalencePathEndpoint _ 1 =
      dgKappaNativeMoritaArrowFamily R s :=
  (dgKappaNativePFamily_exists R s (dgKappaNativeMoritaArrowFamily R s)
    (dgKappaNativeMoritaArrowFamily_at R s)).choose_spec.2.1

lemma dgKappaNativePComparisonFamily_at (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaNativePComparisonFamily R s).app (Opposite.op ⦋0⦌) (coherentNerveVertex A) =
      dgKappaNativePComparisonPath R A (s A).cone (s A).perfect :=
  (dgKappaNativePFamily_exists R s (dgKappaNativeMoritaArrowFamily R s)
    (dgKappaNativeMoritaArrowFamily_at R s)).choose_spec.2.2.1 A

/-- 各対象で元の P と Yoneda の同じ全合成を回収する全入力 arrow 族。 -/
def dgKappaNativePArrowFamily : dgKInputInfinity.{u, max (u + 1) v} R ⟶
    (ihom (Δ[1] : SSet.{max (u + 1) v + 1})).obj _root_.SerrePositivity.InfinityCategories.Stable.Infinity.StableInfinity.{max (u + 1) v} :=
  dgKappaNativePComparisonFamily R s ≫ equivalencePathEndpoint _ 0

lemma dgKappaNativePArrowFamily_at (A : PerfDGInput.{u, max (u + 1) v} R) :
    (dgKappaNativePArrowFamily R s).app (Opposite.op ⦋0⦌) (coherentNerveVertex A) =
      functorVertex (SSet.yonedaEquiv.symm
        (_root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableArrow (dgKappaNativePExactMap R A (s A).cone (s A).perfect)).edge) :=
  (dgKappaNativePFamily_exists R s (dgKappaNativeMoritaArrowFamily R s)
    (dgKappaNativeMoritaArrowFamily_at R s)).choose_spec.2.2.2 A

/-- P/Yoneda の全族は、両端の全入力作用を実 Morita 全族と厳密に共有する。 -/
lemma dgKappaNativePArrowFamily_boundary :
    dgKappaNativePArrowFamily R s ≫ (pre (boundary 1).ι).app _ =
      dgKappaNativeMoritaArrowFamily R s ≫ (pre (boundary 1).ι).app _ := by
  rw [dgKappaNativePArrowFamily, Category.assoc, ← equivalencePathMap_endpoint,
    ← Category.assoc, dgKappaNativePComparisonFamily_boundary]
  simp only [Category.assoc, equivalencePathRefl_endpoint, Category.comp_id]

/-- 元の全 P/Yoneda 作用と実 Morita 全族との、全 native 入力に自然な指定同型。 -/
def dgKappaNativePComparisonFamily_iso :
    FunctorIso (dgKappaNativePArrowFamily R s) (dgKappaNativeMoritaArrowFamily R s) := by
  have h := F1B.kanEquivalencePath_functorIso (dgKappaNativePComparisonFamily R s)
  rw [dgKappaNativePComparisonFamily_one] at h
  exact h

end SerrePositivity.InfinityCategories

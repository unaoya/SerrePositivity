module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalPrismOld

/-!
概要：両円柱を比較する普遍族は、元の始点全余錐でも全パラメーターで定値。
方針：実余錐の旧領域の固定条件を、同じ全円柱の始点包含で読む。
規約：始点の全変換を固定。使われ方：指定始点評価図式の下での比較の整合性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)
local notation "S" => indArrowTerminalLiftFamily W
local notation "A" => arrowInterpolationCorner T
local notation "b" => joinInl A Δ[0] ≫ indArrowSlicePrismBaseCone (q := q)

/-- 同じ全始点余錐の上では、比較普遍族は元の全変換に全次数で定値。 -/
lemma indArrowTerminalPrismFamily_source :
    ((SSet.ι₀ : join T (Δ[0] : SSet.{u + 1}) ⟶ join T Δ[0] ⊗ Δ[1]) ▷ S) ≫
      indArrowTerminalPrismFamily W =
        fst (join T Δ[0]) S ≫ SSet.ι₀ ≫ indArrowNormalizedPrism κ D q := by
  have hb : pushout.inr SSet.ι₀ (joinInl T (Δ[0] : SSet.{u + 1})) ≫ b =
      SSet.ι₀ ≫ indArrowNormalizedPrism κ D q := by
    rw [indArrowSlicePrismBaseCone_old, ← Category.assoc,
      arrowInterpolationCornerInclusion_source]
  have hi := congrArg (fun f ↦ (f ▷ S) ≫ indArrowTerminalCoconeFamily W)
    (arrowInterpolationCoconeIso_inv_source T)
  have hπ : (pushout.inr SSet.ι₀ (joinInl T Δ[0]) ▷ S) ≫ fst A S =
      fst (join T (Δ[0] : SSet.{u + 1})) S ≫
        (pushout.inr SSet.ι₀ (joinInl T Δ[0]) : join T Δ[0] ⟶ A) := by rfl
  calc
    _ = (pushout.inr SSet.ι₀ (joinInl T Δ[0]) ▷ S) ≫
        (joinInl A Δ[0] ▷ S) ≫ indArrowTerminalCoconeFamily W := by
      simpa only [indArrowTerminalPrismFamily, comp_whiskerRight, Category.assoc] using hi
    _ = (pushout.inr SSet.ι₀ (joinInl T Δ[0]) ▷ S) ≫ fst A S ≫ b := by
      rw [indArrowTerminalCoconeFamily_old]
    _ = fst (join T Δ[0]) S ≫ pushout.inr SSet.ι₀ (joinInl T Δ[0]) ≫ b := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ b) hπ
    _ = _ := congrArg (fun f ↦ fst (join T (Δ[0] : SSet.{u + 1})) S ≫ f) hb

/-- 同じ始点全余錐の固定条件を、元の全関手空間の curry 上で読む。 -/
lemma indArrowTerminalPrismCurry_source : curry (indArrowTerminalPrismFamily W) ≫
    (pre (SSet.ι₀ : join T (Δ[0] : SSet.{u + 1}) ⟶ join T Δ[0] ⊗ Δ[1])).app
      (IndInfinity κ C) = SSet.const (functorVertex (SSet.ι₀ ≫ indArrowNormalizedPrism κ D q)) := by
  apply uncurry_injective
  rw [uncurry_pre_app, uncurry_curry, indArrowTerminalPrismFamily_source,
    uncurry_const_functorVertex]

end SerrePositivity.InfinityCategories.F2.Ind

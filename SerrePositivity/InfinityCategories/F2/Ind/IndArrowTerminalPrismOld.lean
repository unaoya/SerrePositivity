module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalPrismFamily
public import SerrePositivity.InfinityCategories.F2.Ind.ArrowInterpolationInverseBoundary

/-!
概要：帰還した普遍全円柱は、元の C 側の全図式を全パラメーターで固定する。
方針：普遍相対 uncurry の底の等式と全円柱同型の元の境界の式を使う。
規約：元の q の全 C 図式を保持。使われ方：元の diagram comma の全族への帰還。
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
local notation "p" => stdSimplex.δ 0 ≫ (liftedIntervalToSmall ≫ D)
local notation "b" => joinInl A Δ[0] ≫ indArrowSlicePrismBaseCone (q := q)

/-- 普遍全余錐の元の領域側は、元の同じ全底図式に全次数で固定される。 -/
lemma indArrowTerminalCoconeFamily_old :
    (joinInl A Δ[0] ▷ S) ≫ indArrowTerminalCoconeFamily W = fst A S ≫ b := by
  let h := indArrowTerminalSliceFamily W
  let R := relativeFunctorSpace (sliceOverProjection p) b
  have hs : (joinInl A Δ[0] ▷ S) ≫ (join A Δ[0] ◁ h) =
      (A ◁ h) ≫ (joinInl A Δ[0] ▷ R) := by rfl
  have ho := congrArg (fun f => (A ◁ h) ≫ f) (relativeSliceCoconeUncurry_old p b)
  calc
    _ = (A ◁ h) ≫ (joinInl A Δ[0] ▷ R) ≫ relativeSliceCoconeUncurry p b := by
      simpa only [indArrowTerminalCoconeFamily, h, Category.assoc] using
        congrArg (fun f => f ≫ relativeSliceCoconeUncurry p b) hs
    _ = (A ◁ h) ≫ fst A R ≫ b := by simpa only [Category.assoc] using ho
    _ = _ := by rw [whiskerLeft_fst_assoc]

/-- 元の試験族側の全円柱は、元の同じ C 全図式の Yoneda 像に全次数で定値。 -/
lemma indArrowTerminalPrismFamily_old :
    ((joinInl T (Δ[0] : SSet.{u + 1}) ▷ Δ[1]) ▷ S) ≫ indArrowTerminalPrismFamily W =
      fst (T ⊗ (Δ[1] : SSet.{u + 1})) S ≫ indArrowOriginalFamily κ D q ≫ indYoneda κ C := by
  have hb : pushout.inl SSet.ι₀ (joinInl T (Δ[0] : SSet.{u + 1})) ≫ b =
      indArrowOriginalFamily κ D q ≫ indYoneda κ C := by
    rw [indArrowSlicePrismBaseCone_old, ← Category.assoc,
      arrowInterpolationCornerInclusion_old, indArrowNormalizedPrism_old]
  have hi := congrArg (fun f => (f ▷ S) ≫ indArrowTerminalCoconeFamily W)
    (arrowInterpolationCoconeIso_inv_old T)
  have hπ : (pushout.inl SSet.ι₀ (joinInl T Δ[0]) ▷ S) ≫ fst A S =
      fst (T ⊗ (Δ[1] : SSet.{u + 1})) S ≫
        (pushout.inl SSet.ι₀ (joinInl T Δ[0]) : T ⊗ Δ[1] ⟶ A) := by rfl
  calc
    _ = (pushout.inl SSet.ι₀ (joinInl T Δ[0]) ▷ S) ≫
        (joinInl A Δ[0] ▷ S) ≫ indArrowTerminalCoconeFamily W := by
      simpa only [indArrowTerminalPrismFamily, comp_whiskerRight, Category.assoc] using hi
    _ = (pushout.inl SSet.ι₀ (joinInl T Δ[0]) ▷ S) ≫ fst A S ≫ b := by
      rw [indArrowTerminalCoconeFamily_old]
    _ = fst (T ⊗ (Δ[1] : SSet.{u + 1})) S ≫
        pushout.inl SSet.ι₀ (joinInl T Δ[0]) ≫ b := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ b) hπ
    _ = _ := congrArg (fun f => fst (T ⊗ (Δ[1] : SSet.{u + 1})) S ≫ f) hb

end SerrePositivity.InfinityCategories.F2.Ind

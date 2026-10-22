module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowTerminalPrismOld

/-!
概要：終端辺固定 fiber の指定頂点で、普遍全余錐と円柱を元の全写像として回収する。
方針：普遍相対評価の頂点公式と全円柱同型を使う。
規約：頂点での対応も厳密な全射の等式。使われ方：元の q の両端の比較。
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
local notation "A" => arrowInterpolationCorner T
local notation "S" => indArrowTerminalLiftFamily W
local notation "p" => stdSimplex.δ 0 ≫ (liftedIntervalToSmall ≫ D)
local notation "b" => indArrowSlicePrismBaseCone (q := q)
local notation "j" => joinInl A Δ[0]
local notation "i" => joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0])
variable (g : join (arrowInterpolationCorner T) (Δ[0] : SSet.{u + 1}) ⟶
    sliceOver (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)))
  (hg : g ≫ sliceOverProjection (stdSimplex.δ 0 ≫ (liftedIntervalToSmall.{u} ≫ D)) =
    indArrowSlicePrismBaseCone (q := q))
  (he : joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0]) ≫ g =
    joinMap (arrowInterpolationSourceTip T) (𝟙 Δ[0]) ≫ indArrowSlicePrismCone W)
local notation "v" => relativeLiftFixedBoundaryVertex (sliceOverProjection p) b i
  (indArrowSlicePrismCone W) (indArrowSlicePrismCone_projection W) g hg he

/-- 制限した普遍族の指定頂点は、元の同じ領域側の相対関手そのもの。 -/
lemma indArrowTerminalSliceFamily_vertex :
    (indArrowTerminalSliceFamily W).app (Opposite.op ⦋0⦌) v =
      relativeFunctorVertex (sliceOverProjection p) (j ≫ b) (j ≫ g)
        (by rw [Category.assoc, hg]) := by
  change (relativeFunctorPre (sliceOverProjection p) b j).app (Opposite.op ⦋0⦌)
    (relativeFunctorVertex (sliceOverProjection p) b g hg) = _
  rw [relativeFunctorPre_vertex]

/-- 普遍全余錐の指定頂点での全射は、元の領域の slice 関手の uncurry そのもの。 -/
lemma indArrowTerminalCoconeFamily_vertex :
    (join A Δ[0] ◁ SSet.yonedaEquiv.symm v) ≫ indArrowTerminalCoconeFamily W =
      fst (join A Δ[0]) Δ[0] ≫ sliceOverUncurry (j ≫ g) := by
  let h := indArrowTerminalSliceFamily W
  have hm : SSet.yonedaEquiv.symm v ≫ h = SSet.yonedaEquiv.symm
      (relativeFunctorVertex (sliceOverProjection p) (j ≫ b) (j ≫ g)
        (by rw [Category.assoc, hg])) := by
    rw [SSet.yonedaEquiv_symm_comp]
    exact congrArg SSet.yonedaEquiv.symm (indArrowTerminalSliceFamily_vertex W g hg he)
  have hw : (join A Δ[0] ◁ SSet.yonedaEquiv.symm v) ≫ (join A Δ[0] ◁ h) =
      join A Δ[0] ◁ (SSet.yonedaEquiv.symm v ≫ h) := by rw [whiskerLeft_comp]
  calc
    _ = (join A Δ[0] ◁ (SSet.yonedaEquiv.symm v ≫ h)) ≫
        relativeSliceCoconeUncurry p (j ≫ b) := by
      simpa only [indArrowTerminalCoconeFamily, h, Category.assoc] using
        congrArg (fun f => f ≫ relativeSliceCoconeUncurry p (j ≫ b)) hw
    _ = _ := by rw [hm]; exact relativeSliceCoconeUncurry_vertex p (j ≫ b) (j ≫ g) _

/-- 帰還した普遍円柱の指定頂点は、元の同じ slice 関手から再構成する全円柱。 -/
lemma indArrowTerminalPrismFamily_vertex :
    ((join T (Δ[0] : SSet.{u + 1}) ⊗ Δ[1]) ◁ SSet.yonedaEquiv.symm v) ≫
      indArrowTerminalPrismFamily W = fst (join T Δ[0] ⊗ Δ[1]) Δ[0] ≫
        (arrowInterpolationCoconeIso T).inv ≫ sliceOverUncurry (j ≫ g) := by
  have hs : ((join T Δ[0] ⊗ Δ[1]) ◁ SSet.yonedaEquiv.symm v) ≫
      ((arrowInterpolationCoconeIso T).inv ▷ S) =
        ((arrowInterpolationCoconeIso T).inv ▷ Δ[0]) ≫
          (join A Δ[0] ◁ SSet.yonedaEquiv.symm v) := by rfl
  calc
    _ = ((arrowInterpolationCoconeIso T).inv ▷ Δ[0]) ≫
        (join A Δ[0] ◁ SSet.yonedaEquiv.symm v) ≫ indArrowTerminalCoconeFamily W := by
      simpa only [indArrowTerminalPrismFamily, Category.assoc] using
        congrArg (fun f => f ≫ indArrowTerminalCoconeFamily W) hs
    _ = _ := by rw [indArrowTerminalCoconeFamily_vertex, whiskerRight_fst_assoc]

end SerrePositivity.InfinityCategories.F2.Ind

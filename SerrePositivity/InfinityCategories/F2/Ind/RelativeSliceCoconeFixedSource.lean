module

public import SerrePositivity.InfinityCategories.F2.Ind.RelativeSliceCoconeSourceRestriction
public import SerrePositivity.InfinityCategories.F2.Ind.RelativeSliceCoconeBoundaryVertex

/-!
概要：元の部分領域で定値な相対 slice 関手の全族は、その右余錐全体でも定値。
方針：普遍 uncurry の形状自然性と元の頂点の厳密な評価を使う。
規約：全次数の固定条件。使われ方：元の全区間 D を固定する族の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ相対頂点に定値な普遍族は、元の同じ全余錐に定値となる。 -/
lemma relativeSliceCoconeUncurry_constant {A S X : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X) (f : A ⟶ sliceOver p)
    (hf : f ≫ sliceOverProjection p = b) :
    (join A Δ[0] ◁ (SSet.const (relativeFunctorVertex (sliceOverProjection p) b f hf) : S ⟶ _)) ≫
      relativeSliceCoconeUncurry p b = fst (join A Δ[0]) S ≫ sliceOverUncurry f := by
  have hv := congrArg Subtype.val (relativeSliceCoconeBoundaryMap_vertex p b f hf)
  have hc : (SSet.const (relativeFunctorVertex (sliceOverProjection p) b f hf) : S ⟶ _) ≫
      curry (relativeSliceCoconeUncurry p b) = SSet.const (functorVertex (sliceOverUncurry f)) := by
    rw [SSet.const_comp]
    exact congrArg (fun v => SSet.const v) hv
  simpa only [uncurry_natural_left, uncurry_curry, uncurry_const_functorVertex] using
    congrArg uncurry hc

/-- 指定部分領域への相対制限が定値なら、その右余錐全体の族も厳密に定値。 -/
lemma relativeSliceCoconeUncurry_fixedSource {A K S X : SSet.{u}}
    (p : (Δ[0] : SSet.{u}) ⟶ X) (b : A ⟶ X) (a : K ⟶ A)
    (h : S ⟶ relativeFunctorSpace (sliceOverProjection p) b)
    (g : K ⟶ sliceOver p) (hg : g ≫ sliceOverProjection p = a ≫ b)
    (hh : h ≫ relativeFunctorPre (sliceOverProjection p) b a =
      SSet.const (relativeFunctorVertex (sliceOverProjection p) (a ≫ b) g hg)) :
    (joinMap a (𝟙 Δ[0]) ▷ S) ≫ (join A Δ[0] ◁ h) ≫ relativeSliceCoconeUncurry p b =
      fst (join K Δ[0]) S ≫ sliceOverUncurry g := by
  have hs : (joinMap a (𝟙 Δ[0]) ▷ S) ≫ (join A Δ[0] ◁ h) =
      (join K Δ[0] ◁ h) ≫ (joinMap a (𝟙 Δ[0]) ▷ _) := by rfl
  rw [← Category.assoc, hs, Category.assoc, relativeSliceCoconeUncurry_source,
    ← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hh]
  exact relativeSliceCoconeUncurry_constant p (a ≫ b) g hg

end SerrePositivity.InfinityCategories.F2.Ind

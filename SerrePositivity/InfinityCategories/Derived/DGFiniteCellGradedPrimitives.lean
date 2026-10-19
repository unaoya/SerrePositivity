module
public import SerrePositivity.InfinityCategories.Derived.DGFiniteCellTargetDenominator
public import SerrePositivity.InfinityCategories.Derived.DGModuleClosedRightShift
public import SerrePositivity.InfinityCategories.Derived.DGModuleRightShiftBoundaries
public import SerrePositivity.InfinityCategories.Derived.DGRepresentableDerivedPrimitives

/-! # 有限 cell 加群標的の斉次閉元の実分母後の原始元

概要：表現可能加群から有限 cell 標的への任意次数の閉元を、元の閉分母で境界にする。
方針：標的シフトへの閉射を導来零化し、始域の射影性から具体的な原始元を回収する。
規約：商と K-flat 性は不要。使われ方：最後外ホーンの加群 cone 残差の消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 表現可能始域の全 Hom 元に、元の閉射の Yoneda 像を前合成する。 -/
def dgRepresentableModulePrecompose {q x : D} {M : RightModule A D} (n : ℤ)
    (f : GradedHom A (representable A x) M n)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    GradedHom A (representable A q) M n :=
  compose A f (closedHomEquiv A (RightModule A D) _ _
    ((dgYoneda A D).onClosed.map s)).val (zero_add n)

variable [IsDGPretriangulated A D]

/-- 指定有限 cell 標的の斉次閉元は、元の実閉分母の前合成後に具体的な境界になる。 -/
theorem dgFiniteCellGraded_exists_closedPrimitive (P : Set D) (x : D)
    (M : ModuleCategory A D)
    (hM : derivedFiniteCellOver A D P ((moduleToDerived A D).obj M))
    (n k : ℤ) (hkn : k + 1 = n)
    (f : GradedHom A (representable A x) (ForgetEnrichment.to (Complex A) M) n)
    (hf : differential A f = 0) :
    ∃ (q : D) (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x),
      (dgClosedEdge A D s).edge ∈ dgVerdierEdges A D P ∧
        ∃ h : GradedHom A (representable A q) (ForgetEnrichment.to (Complex A) M) k,
          (moduleHom A D (representable A q) (ForgetEnrichment.to (Complex A) M)).d k n h =
            dgRepresentableModulePrecompose A D n f s := by
  let F := moduleToDerived A D
  let c := dgModuleClosedRightShift A D n f hf
  have hshift : derivedFiniteCellOver A D P (F.obj (M⟦n⟧)) :=
    (derivedFiniteCellOver A D P).prop_of_iso ((F.commShiftIso n).app M).symm
      ((derivedFiniteCellOver A D P).le_shift n _ hM)
  obtain ⟨q, s, hs, hz⟩ := dgFiniteCellTarget_exists_closedDenominator A D P x hshift (F.map c)
  let t := (dgYoneda A D).onClosed.map s
  have hz' : F.map (t ≫ c) = 0 := by
    rw [Functor.map_comp]
    exact hz
  obtain ⟨b, hb⟩ := (dgModuleProjectiveDerived_zero_iff_primitive A D
    (representable_homotopicallyProjective A D q) (t ≫ c)).mp hz'
  refine ⟨q, s, hs, ?_⟩
  apply (dgModuleHomRightShift_exists_primitive_iff A D n k hkn
    (dgRepresentableModulePrecompose A D n f s)).mp
  exact ⟨b, hb.trans (dgModuleClosedRightShift_precompose_cycle A D n f hf t)⟩

end SerrePositivity.InfinityCategories

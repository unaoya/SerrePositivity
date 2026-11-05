module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanBoundarySlice
public import SerrePositivity.KST.LocalizingInvariants.SliceConeDiagramRestriction
public import SerrePositivity.InfinityCategories.F2.Idempotent.PointSliceArrows

/-!
概要：実分母族から元の固定端点 span への標準比較を、全錐図式の上で照合する。
方針：全部分複体・厳密 fiber の同型の包含を計算し、元の slice 比較に戻す。
規約：全次数と全パラメータの図式を保持する。
使われ方：分母・次辺を共有経路つき単体貼合せへ渡す際の実比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 固定 marked span と全錐の厳密同型は、元の全 span 図式をそのまま移す。 -/
lemma fixedMarkedSpanConeFamilyIso_hom_ambient (X : SSet.{u})
    (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    (fixedMarkedSpanConeFamilyIso X W x y).hom ≫ (markedSpanConeFamily W x y).ι ≫
      vertexFiberι (coneRestriction (boundary 1 : SSet.{u}) X)
        (functorVertex (intervalMappingBoundary x y)) =
      fixedMarkedSpanInclusion X W x y ≫ markedSpanInclusion X W ≫
        (pre spanBoundaryConeIso.hom).app X := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  rfl

lemma fixedMarkedSpanConeFamilyIso_inv_ambient (X : SSet.{u})
    (W : Set (X _⦋1⦌)) (x y : X _⦋0⦌) :
    (fixedMarkedSpanConeFamilyIso X W x y).inv ≫
      fixedMarkedSpanInclusion X W x y ≫ markedSpanInclusion X W ≫
        (pre spanBoundaryConeIso.hom).app X =
      (markedSpanConeFamily W x y).ι ≫
        vertexFiberι (coneRestriction (boundary 1 : SSet.{u}) X)
          (functorVertex (intervalMappingBoundary x y)) := by
  apply (cancel_epi (fixedMarkedSpanConeFamilyIso X W x y).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  exact fixedMarkedSpanConeFamilyIso_hom_ambient X W x y

/-- 元の標準 span 比較の全錐図式は、実境界 slice の同じ標準比較そのもの。 -/
lemma verdierDenominatorSpanCanonicalComparison_diagram
    {A B : StableCategory.{u}} (i : ExactMap A B) (x y : B.obj _⦋0⦌) :
    verdierDenominatorSpanCanonicalComparison i x y ≫
      fixedMarkedSpanInclusion B.obj (weakEquivalences i) x y ≫
      markedSpanInclusion B.obj (weakEquivalences i) ≫
      (pre spanBoundaryConeIso.hom).app B.obj =
    (verdierDenominatorSpanBoundaryIso i x y).hom ≫
      (markedSpanSlice (weakEquivalences i) x y).ι ≫
      sliceConeDiagramMap (intervalMappingBoundary x y) := by
  rw [verdierDenominatorSpanCanonicalComparison, markedSpanSliceToFixed]
  simp only [Category.assoc]
  rw [fixedMarkedSpanConeFamilyIso_inv_ambient]
  rw [← Category.assoc (markedSpanSliceConeComparison (weakEquivalences i) x y),
    markedSpanSliceConeComparison_ι]
  rfl

/-- 同じ二点表示から境界表示への輸送は、任意の実錐族の展開を保持する。 -/
lemma spanBoundarySliceIso_uncurry {X T : SSet.{u}} (x y : X _⦋0⦌)
    (F : T ⟶ sliceOver (spanTwoPointDiagram x y)) :
    sliceOverUncurry (F ≫ (spanBoundarySliceIso x y).hom) =
      joinMap (𝟙 T) spanEndpointCoproductIso.inv ≫ sliceOverUncurry F := by
  dsimp only [spanBoundarySliceIso, F1B.sliceDiagramIso, Iso.trans_hom, asIso_hom, eqToIso]
  simp only [← Category.assoc]
  rw [sliceOverUncurry_eqToHom, sliceOverUncurry_restrict, sliceOverUncurry_postcomp]
  · simp only [Iso.refl_hom, Category.comp_id]
  · rw [spanEndpointCoproductDiagram_eq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- 区間境界の始点への実 slice 制限。 -/
def spanBoundarySliceLeft {X : SSet.{u}} (x y : X _⦋0⦌) :
    sliceOver (intervalMappingBoundary x y) ⟶ sliceOver (SSet.yonedaEquiv.symm x) :=
  sliceOverRestrict (intervalMappingBoundary x y) (boundary.ι (1 : Fin 2)) ≫
    eqToHom (congrArg sliceOver (intervalMappingBoundary_face_one x y))

/-- 区間境界の終点への実 slice 制限。 -/
def spanBoundarySliceRight {X : SSet.{u}} (x y : X _⦋0⦌) :
    sliceOver (intervalMappingBoundary x y) ⟶ sliceOver (SSet.yonedaEquiv.symm y) :=
  sliceOverRestrict (intervalMappingBoundary x y) (boundary.ι (0 : Fin 2)) ≫
    eqToHom (congrArg sliceOver (intervalMappingBoundary_face_zero x y))

lemma spanBoundarySliceIso_left {X : SSet.{u}} (x y : X _⦋0⦌) :
    (spanBoundarySliceIso x y).hom ≫ spanBoundarySliceLeft x y =
      sliceOverCoproductLeft (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y) := by
  apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm x)
  have hb := spanBoundarySliceIso_uncurry x y (𝟙 (sliceOver (spanTwoPointDiagram x y)))
  simp only [Category.id_comp] at hb
  have hc := sliceOverCoproductLeft_uncurry (SSet.yonedaEquiv.symm x)
    (SSet.yonedaEquiv.symm y) (𝟙 (sliceOver (spanTwoPointDiagram x y)))
  simp only [Category.id_comp] at hc
  rw [spanBoundarySliceLeft, ← Category.assoc, sliceOverUncurry_eqToHom,
    sliceOverUncurry_restrict, hb, hc, ← Category.assoc, ← joinMap_comp,
    Category.id_comp, ← spanEndpointCoproductIso_left, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  exact intervalMappingBoundary_face_one x y

lemma spanBoundarySliceIso_right {X : SSet.{u}} (x y : X _⦋0⦌) :
    (spanBoundarySliceIso x y).hom ≫ spanBoundarySliceRight x y =
      sliceOverCoproductRight (SSet.yonedaEquiv.symm x) (SSet.yonedaEquiv.symm y) := by
  apply sliceOverUncurry_injective (SSet.yonedaEquiv.symm y)
  have hb := spanBoundarySliceIso_uncurry x y (𝟙 (sliceOver (spanTwoPointDiagram x y)))
  simp only [Category.id_comp] at hb
  have hc := sliceOverCoproductRight_uncurry (SSet.yonedaEquiv.symm x)
    (SSet.yonedaEquiv.symm y) (𝟙 (sliceOver (spanTwoPointDiagram x y)))
  simp only [Category.id_comp] at hc
  rw [spanBoundarySliceRight, ← Category.assoc, sliceOverUncurry_eqToHom,
    sliceOverUncurry_restrict, hb, hc, ← Category.assoc, ← joinMap_comp,
    Category.id_comp, ← spanEndpointCoproductIso_right, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]
  exact intervalMappingBoundary_face_zero x y

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedMarkedSpanConeFamilyIso_hom_ambient := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedMarkedSpanConeFamilyIso_hom_ambient

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fixedMarkedSpanConeFamilyIso_inv_ambient := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fixedMarkedSpanConeFamilyIso_inv_ambient

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceIso_left := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceIso_right := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceIso_uncurry := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceIso_uncurry

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceLeft (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceLeft := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceLeft

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceRight (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceRight := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceRight

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierDenominatorSpanCanonicalComparison_diagram := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison_diagram

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceLeft._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceLeft._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceLeft._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceLeft._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceLeft.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceLeft.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceRight._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceRight._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanBoundarySliceRight.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanBoundarySliceRight.eq_1

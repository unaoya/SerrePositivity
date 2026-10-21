module
public import SerrePositivity.KST.SConstruction.PointedBasedActionFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGOneDirectionReducedEnrichedFunctor

/-! # 元の一次方向の境界商への標準点つき厳密豊穣関手
概要：同じ境界商と全 native basedHom 族を、標準の点つき豊穣関手へ束ねる。
方針：包含後に検証済みの単位・合成を標準 basedHom に反映する。
規約：元の点つき値・通常射を変更しない。使われ方：点つき Kan 置換と BF K。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の同じ点つき境界商を標準の点つき対象として保持する。 -/
def presentedPerfectDGOneDirectionPointedObject (r : ℕ) (C : PerfDGInput.{u, v} A) :
    PointedSSetObject.{max (u + 1) v} :=
  ⟨oneDirectionReducedRealization r
    (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A C))⟩

/-- 作用法則までを固定し、元の basedHom 包含の回収式だけを入力に残す包装。 -/
def presentedPerfectDGOneDirectionPointedFunctorBuilder (r : ℕ) :=
  pointedEnrichedFunctorOfBasedAction (C := PerfDGInput.{u, v} A)
    (presentedPerfectDGOneDirectionPointedObject.{u, v} A r)
    (presentedPerfectDGOneDirectionReducedAction.{u, v} A r)
    (presentedPerfectDGOneDirectionReducedAction_unit.{u, v} A r)
    (presentedPerfectDGOneDirectionReducedAction_comp.{u, v} A r)
    (presentedPerfectDGOneDirectionReducedFamilyMap.{u, v} A r)

/-- 元の同じ点つき商と全 native 入力族を持つ、標準の厳密点つき豊穣関手。 -/
def presentedPerfectDGOneDirectionPointedEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{max (u + 1) v} (PerfDGInput.{u, v} A)
      PointedSSetObject.{max (u + 1) v} :=
  presentedPerfectDGOneDirectionPointedFunctorBuilder.{u, v} A r
    (presentedPerfectDGOneDirectionReducedFamilyMap_inclusion.{u, v} A r)

/-- 標準点つき関手の実値は、同じ元の点つき境界商。 -/
lemma presentedPerfectDGOneDirectionPointedEnrichedFunctor_obj (r : ℕ)
    (C : PerfDGInput.{u, v} A) :
    ((presentedPerfectDGOneDirectionPointedEnrichedFunctor.{u, v} A r).obj C).obj =
      oneDirectionReducedRealization r
        (stableCategoryModel (presentedPerfectDGStableCategory.{u, v} A C)) := rfl

/-- 標準 basedHom への作用は、同じ元の全 native 基点固定写像族。 -/
lemma presentedPerfectDGOneDirectionPointedEnrichedFunctor_map (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    (presentedPerfectDGOneDirectionPointedEnrichedFunctor.{u, v} A r).map C D =
      presentedPerfectDGOneDirectionReducedFamilyMap.{u, v} A r C D := rfl

/-- 標準の点つき値で表した全作用は、同じ元の通常 dg 商射を回収する。 -/
lemma presentedPerfectDGOneDirectionPointedAction_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    (𝟙 (presentedPerfectDGOneDirectionPointedObject.{u, v} A r C).obj.right ⊗ₘ
      eHomEquiv SSet.{max (u + 1) v} F) ≫
      presentedPerfectDGOneDirectionReducedAction.{u, v} A r C D =
    (ρ_ (presentedPerfectDGOneDirectionPointedObject.{u, v} A r C).obj.right).hom ≫
      (presentedPerfectDGOneDirectionPointedMap.{u, v} A r F).right :=
  presentedPerfectDGOneDirectionReducedAction_hom.{u, v} A r F

/-- 標準点つき値の包含後に、同じ元の全作用を回収する。 -/
lemma presentedPerfectDGOneDirectionPointedFamily_inclusion (r : ℕ)
    (C D : PerfDGInput.{u, v} A) :
    presentedPerfectDGOneDirectionReducedFamilyMap.{u, v} A r C D ≫
      PointedObject.basedHomι
        (presentedPerfectDGOneDirectionPointedObject.{u, v} A r C).obj
        (presentedPerfectDGOneDirectionPointedObject.{u, v} A r D).obj =
      curry (presentedPerfectDGOneDirectionReducedAction.{u, v} A r C D) :=
  presentedPerfectDGOneDirectionReducedFamilyMap_inclusion.{u, v} A r C D

/-- 通常射の回収で、同じ入力族と作用を先に固定する。 -/
def presentedPerfectDGOneDirectionPointedHomBuilder (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :=
  pointedBasedFamily_hom
    (X := presentedPerfectDGOneDirectionPointedObject.{u, v} A r C)
    (Y := presentedPerfectDGOneDirectionPointedObject.{u, v} A r D)
    (P := C ⟶[SSet.{max (u + 1) v}] D)
    (eHomEquiv SSet.{max (u + 1) v} F)
    (presentedPerfectDGOneDirectionReducedAction.{u, v} A r C D)
    (presentedPerfectDGOneDirectionReducedFamilyMap.{u, v} A r C D)

/-- 同じ全族の包含を固定し、通常の点つき射の指定だけを残す。 -/
def presentedPerfectDGOneDirectionPointedHomRecovery (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :=
  presentedPerfectDGOneDirectionPointedHomBuilder.{u, v} A r F
    (presentedPerfectDGOneDirectionPointedFamily_inclusion.{u, v} A r C D)

/-- 元の通常の点つき射を指定した、残る作用回収式による検出。 -/
def presentedPerfectDGOneDirectionPointedHomRecoveryMap (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :=
  presentedPerfectDGOneDirectionPointedHomRecovery.{u, v} A r F
    (presentedPerfectDGOneDirectionPointedMap.{u, v} A r F)

/-- 元の作用回収式を適用した、標準点つき Hom の実際の回収証明。 -/
def presentedPerfectDGOneDirectionPointedHomRecovered (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :=
  presentedPerfectDGOneDirectionPointedHomRecoveryMap.{u, v} A r F
    (presentedPerfectDGOneDirectionPointedAction_hom.{u, v} A r F)

/-- 通常の厳密 dg 入力射は、同じ元の点つき境界商の射として回収される。 -/
lemma presentedPerfectDGOneDirectionPointedEnrichedFunctor_hom (r : ℕ)
    {C D : PerfDGInput.{u, v} A} (F : C ⟶ D) :
    eHomEquiv SSet.{max (u + 1) v} F ≫
      (presentedPerfectDGOneDirectionPointedEnrichedFunctor.{u, v} A r).map C D =
        eHomEquiv SSet.{max (u + 1) v}
          (show presentedPerfectDGOneDirectionPointedObject.{u, v} A r C ⟶
            presentedPerfectDGOneDirectionPointedObject.{u, v} A r D from
            presentedPerfectDGOneDirectionPointedMap.{u, v} A r F) := by
  change eHomEquiv SSet.{max (u + 1) v} F ≫
    presentedPerfectDGOneDirectionReducedFamilyMap.{u, v} A r C D = _
  exact presentedPerfectDGOneDirectionPointedHomRecovered.{u, v} A r F

/-- 基礎単体集合へ忘れると、供給済みの同じ元の閉 Hom 値豊穣関手になる。 -/
lemma presentedPerfectDGOneDirectionPointedEnrichedFunctor_forget (r : ℕ) :
    (presentedPerfectDGOneDirectionPointedEnrichedFunctor.{u, v} A r).comp SSet
      pointedSSetObjectClosedForget =
      presentedPerfectDGOneDirectionReducedEnrichedFunctor.{u, v} A r := by
  refine EnrichedFunctor.ext SSet (fun _ => rfl) ?_
  intro C D
  exact (Category.comp_id _).trans
    (presentedPerfectDGOneDirectionReducedEnrichedFunctor_family.{u, v} A r C D)

end SerrePositivity.KST.SConstruction

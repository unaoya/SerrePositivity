module
public import SerrePositivity.KST.SConstruction.DGGluingRightAxisHom
public import SerrePositivity.KST.SConstruction.DGPointedQuotientEnd
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Size

/-! # 元の右対象 End から指定商 End への実 dg 射
概要：元の右軸包含を通し、右対象 b の End を同じ (0,b,0) の商 End へ送る。
方針：同じ全 Hom 作用と元の商射を End へ制限し、商への包含の正方形を照合する。
規約：右対象と零左成分を保持。使われ方：dg ⊙ への元の右端の射。
-/
@[expose] public section
noncomputable section
universe u v w t
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (z : C) (hz : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) z))
  {P : Type t} [DGCategory R P] (i : DGFunctor R P (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)) (b : D)

/-- 元の右対象の全 End を、同じ右軸対象の全 End へ送る実 dg 関手。 -/
def dgGluingRightAxisEndMap :
    DGFunctor R (EndomorphismObject b)
      (EndomorphismObject (dgGluingRightAxisObject R C D M z b)) :=
  endomorphismMap R (dgGluingRightAxis R C D M z hz) b

omit [Small.{u} D] in
/-- 同じ全 End 上の作用は、元の右軸包含の全 Hom 作用そのもの。 -/
lemma dgGluingRightAxisEndMap_map (x y : EndomorphismObject b) :
    (dgGluingRightAxisEndMap R C D M z hz b).map x y =
      (dgGluingRightAxisHomIso R C D M z hz b b).inv :=
  dgGluingRightAxis_map R C D M z hz b b

/-- 元の右対象 End から、元の対角商内の同じ (0,b,0) の End への実 dg 射。 -/
def dgGluingRightQuotientEndMap :
    DGFunctor R (EndomorphismObject b)
      (PointedDGQuotientEndObject R i (dgGluingRightAxisObject R C D M z b)) :=
  (dgGluingRightAxisEndMap R C D M z hz b).comp
    (pointedDGQuotientEndUnitMap R i (dgGluingRightAxisObject R C D M z b))

/-- 同じ実 End 射は、元の右軸 Hom 同型の逆と元の零長 path 包含の合成。 -/
lemma dgGluingRightQuotientEndMap_map (x y : EndomorphismObject b) :
    (dgGluingRightQuotientEndMap R C D M z hz i b).map x y =
      (dgGluingRightAxisHomIso R C D M z hz b b).inv ≫
        DGQuotient.originalHomInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (dgQuotientImage R i)
          (dgGluingRightAxisObject R C D M z b) (dgGluingRightAxisObject R C D M z b) :=
  congrArg (fun k => k ≫ DGQuotient.originalHomInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
    (dgQuotientImage R i) (dgGluingRightAxisObject R C D M z b)
      (dgGluingRightAxisObject R C D M z b)) (dgGluingRightAxis_map R C D M z hz b b)

/-- 同じ End 射を商に含めると、元の右軸包含と商射を厳密に回収する。 -/
lemma dgGluingRightQuotientEndMap_inclusion :
    (dgGluingRightQuotientEndMap R C D M z hz i b).comp
      (pointedDGQuotientEndInclusion R i (dgGluingRightAxisObject R C D M z b)) =
    ((endomorphismInclusion R b).comp (dgGluingRightAxis R C D M z hz)).comp
      (pointedDGQuotientProjection R i) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := (dgGluingRightQuotientEndMap R C D M z hz i b).comp
      (pointedDGQuotientEndInclusion R i (dgGluingRightAxisObject R C D M z b)))
    (G := ((endomorphismInclusion R b).comp (dgGluingRightAxis R C D M z hz)).comp
      (pointedDGQuotientProjection R i)) (fun _ => rfl)
  intro x y
  change (((dgGluingRightAxis R C D M z hz).map b b ≫
    DGQuotient.originalHomInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (dgQuotientImage R i)
      (dgGluingRightAxisObject R C D M z b) (dgGluingRightAxisObject R C D M z b)) ≫ 𝟙 _) ≫
    𝟙 _ = (𝟙 _ ≫ (dgGluingRightAxis R C D M z hz).map b b) ≫
      DGQuotient.originalHomInclusion R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) (dgQuotientImage R i)
        (dgGluingRightAxisObject R C D M z b) (dgGluingRightAxisObject R C D M z b)
  simp only [Category.comp_id, Category.id_comp]

end SerrePositivity.KST.SConstruction

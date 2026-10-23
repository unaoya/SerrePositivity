module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomTensorComparison
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomTargetSpaceComparison
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeHomSourceSpaceComparison
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence
/-!
概要：同じ二入力導来 Hom の基礎空間を、固定入力で元の F1 Hom∞ へ比較する。
方針：D(R) 値の全関手比較を同じ基礎空間へ送り、既存の両側の分類比較へ接続する。
規約：同じ tensor nerve の制限上の全関手比較。元の直積上の同定は別工程。
使われ方：二変数導来 Hom と元の写像空間関手の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve Opposite MonoidalCategory SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 同じ二入力 D(R) 値 Hom の全基礎空間関手。 -/
def dgSemifreeDerivedHomTensorSpaceInfinity :
    (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).obj
      (dgNerve R (DGTensorCategory R (SemifreeDGModules R D)ᵒᵖ (SemifreeDGModules R D))) ⟶
        SpaceInfinity.{max (u + 1) v} :=
  (SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
    (dgSemifreeDerivedHomTensorInfinity R D) ≫ dgHomDerivedSpaceInfinity R D
/-- 同じ固定始域制限は、元の F1 共変 Hom∞ と全関手同型。 -/
def dgSemifreeDerivedHomTensor_targetF1SpaceIso (P : SemifreeDGModules R D) :
    FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgTensorIncludeSecond R (SemifreeDGModules R D)ᵒᵖ
          (SemifreeDGModules R D) (op P))) ≫ dgSemifreeDerivedHomTensorSpaceInfinity R D)
      (dgSemifreeHomTargetF1SpaceInfinity R D P) := by
  have e := ((dgSemifreeDerivedHomTensor_targetIso R D P).ulift).postcomp
    (dgHomDerivedSpaceInfinity R D)
  have e' : FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        (dgNerve.map (dgTensorIncludeSecond R (SemifreeDGModules R D)ᵒᵖ
          (SemifreeDGModules R D) (op P))) ≫ dgSemifreeDerivedHomTensorSpaceInfinity R D)
      (dgSemifreeDerivedHomTargetSpaceInfinity R D P) := by
    simpa only [dgSemifreeDerivedHomTensorSpaceInfinity, dgSemifreeDerivedHomTargetSpaceInfinity,
      CategoryTheory.Functor.map_comp, Category.assoc] using! e
  exact e' ≪≫ dgSemifreeDerivedHomTargetF1SpaceIso R D P
/-- 同じ固定終域制限は、実反対 ∞ 圏上の元の表現可能前層と全関手同型。 -/
def dgSemifreeDerivedHomTensor_sourceF1SpaceIso (Q : SemifreeDGModules R D) :
    FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        ((dgNerveOppositeIso R (SemifreeDGModules R D)).hom ≫
          dgNerve.map (dgTensorIncludeFirst R (SemifreeDGModules R D)ᵒᵖ
            (SemifreeDGModules R D) Q)) ≫ dgSemifreeDerivedHomTensorSpaceInfinity R D)
      (representablePresheafInfinity (dgSemifreeHomVertex R D Q)) := by
  have h := (dgSemifreeDerivedHomTensor_sourceIso R D Q).precomp
    (dgNerveOppositeIso R (SemifreeDGModules R D)).hom
  have e := h.ulift.postcomp (dgHomDerivedSpaceInfinity R D)
  have e' : FunctorIso
      ((SSet.uliftFunctor.{max (u + 1) v + 1, max (u + 1) v}).map
        ((dgNerveOppositeIso R (SemifreeDGModules R D)).hom ≫
          dgNerve.map (dgTensorIncludeFirst R (SemifreeDGModules R D)ᵒᵖ
            (SemifreeDGModules R D) Q)) ≫ dgSemifreeDerivedHomTensorSpaceInfinity R D)
      (dgSemifreeDerivedHomContravariantSpaceInfinity R D Q) := by
    simpa only [dgSemifreeDerivedHomTensorSpaceInfinity,
      dgSemifreeDerivedHomContravariantSpaceInfinity, dgSemifreeDerivedContravariantHomInfinity,
      CategoryTheory.Functor.map_comp, Category.assoc] using! e
  exact e' ≪≫ dgSemifreeDerivedHomContravariantF1SpaceIso R D Q
end SerrePositivity.InfinityCategories

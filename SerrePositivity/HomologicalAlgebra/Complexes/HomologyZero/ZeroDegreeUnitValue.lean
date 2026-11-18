module

public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.ZeroDegreeComplexIso

/-!
# 標準 H⁰ 同型の元の単位からの値

概要：零次集中複体の標準 H⁰ 同型は、元の単位からの射をその実ホモロジー類へ送る。
方針：元の零次成分の写像と単位からの閉元の同値を計算する。
規約：既存 unitClass と同じ値を厳密に回収する。
使われ方：H⁰ の単位と積の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomologyZero
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

def singleUnit (M : ModuleCat.{u} A) (x : M) :
    𝟙_ (Complex A) ⟶ (single (ModuleCat A) (.up ℤ) 0).obj M :=
  unitFromCycle _ ⟨(singleObjXSelf (.up ℤ) 0 M).inv x, by
    change (((single (ModuleCat A) (.up ℤ) 0).obj M).d 0 1).hom _ = 0
    rw [single_obj_d]
    rfl⟩

def singleValue (M : ModuleCat.{u} A)
    (f : 𝟙_ (Complex A) ⟶ (single (ModuleCat A) (.up ℤ) 0).obj M) : M :=
  (singleObjXSelf (.up ℤ) 0 M).hom (cycleFromUnit _ f).val

lemma singleUnit_value (M : ModuleCat.{u} A) (x : M) :
    _root_.SerrePositivity.HomologyZero.singleValue M (_root_.SerrePositivity.HomologyZero.singleUnit M x) = x := by
  unfold _root_.SerrePositivity.HomologyZero.singleValue _root_.SerrePositivity.HomologyZero.singleUnit
  rw [cycleFromUnit_unitFromCycle]
  exact ConcreteCategory.congr_hom (singleObjXSelf (.up ℤ) 0 M).inv_hom_id x

lemma zeroDegreeToSingle_unit_value (K : Complex A) [K.IsStrictlyLE 0] [K.IsStrictlyGE 0]
    (f : 𝟙_ (Complex A) ⟶ K) :
    _root_.SerrePositivity.HomologyZero.singleValue (K.homology 0) (f ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle K) = _root_.SerrePositivity.HomologyZero.unitClass K f := by
  change (singleObjXSelf (.up ℤ) 0 (K.homology 0)).hom
    ((_root_.SerrePositivity.HomologyZero.zeroDegreeToSingle K).f 0 (cycleFromUnit K f).val) = _root_.SerrePositivity.HomologyZero.unitClass K f
  simp only [_root_.SerrePositivity.HomologyZero.zeroDegreeToSingle, mkHomToSingle_f]
  change (singleObjXSelf (.up ℤ) 0 (K.homology 0)).hom
    ((singleObjXSelf (.up ℤ) 0 (K.homology 0)).inv
      (_root_.SerrePositivity.HomologyZero.componentHomologyLinearEquiv K (cycleFromUnit K f).val)) = _root_.SerrePositivity.HomologyZero.unitClass K f
  exact (ConcreteCategory.congr_hom (singleObjXSelf (.up ℤ) 0 (K.homology 0)).inv_hom_id
    (_root_.SerrePositivity.HomologyZero.componentHomologyLinearEquiv K (cycleFromUnit K f).val)).trans
      (_root_.SerrePositivity.HomologyZero.componentHomologyLinearEquiv_unit K f)

lemma zeroDegreeToSingle_unit (K : Complex A) [K.IsStrictlyLE 0] [K.IsStrictlyGE 0]
    (f : 𝟙_ (Complex A) ⟶ K) :
    f ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle K = _root_.SerrePositivity.HomologyZero.singleUnit (K.homology 0) (_root_.SerrePositivity.HomologyZero.unitClass K f) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  apply ((ModuleCat.mono_iff_injective
    (singleObjXSelf (.up ℤ) 0 (K.homology 0)).hom).mp inferInstance)
  change _root_.SerrePositivity.HomologyZero.singleValue (K.homology 0) (f ≫ _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle K) =
    _root_.SerrePositivity.HomologyZero.singleValue (K.homology 0) (_root_.SerrePositivity.HomologyZero.singleUnit (K.homology 0) (_root_.SerrePositivity.HomologyZero.unitClass K f))
  rw [_root_.SerrePositivity.HomologyZero.singleUnit_value, _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle_unit_value]

end SerrePositivity.HomologyZero

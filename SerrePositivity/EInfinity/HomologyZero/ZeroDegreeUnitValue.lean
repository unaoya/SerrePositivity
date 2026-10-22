module

public import SerrePositivity.EInfinity.HomologyZero.ZeroDegreeComplexIso

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
namespace SerrePositivity.EInfinity.HomologyZero
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
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
    singleValue M (singleUnit M x) = x := by
  unfold singleValue singleUnit
  rw [cycleFromUnit_unitFromCycle]
  exact ConcreteCategory.congr_hom (singleObjXSelf (.up ℤ) 0 M).inv_hom_id x

lemma zeroDegreeToSingle_unit_value (K : Complex A) [K.IsStrictlyLE 0] [K.IsStrictlyGE 0]
    (f : 𝟙_ (Complex A) ⟶ K) :
    singleValue (K.homology 0) (f ≫ zeroDegreeToSingle K) = unitClass K f := by
  change (singleObjXSelf (.up ℤ) 0 (K.homology 0)).hom
    ((zeroDegreeToSingle K).f 0 (cycleFromUnit K f).val) = unitClass K f
  simp only [zeroDegreeToSingle, mkHomToSingle_f]
  change (singleObjXSelf (.up ℤ) 0 (K.homology 0)).hom
    ((singleObjXSelf (.up ℤ) 0 (K.homology 0)).inv
      (componentHomologyLinearEquiv K (cycleFromUnit K f).val)) = unitClass K f
  exact (ConcreteCategory.congr_hom (singleObjXSelf (.up ℤ) 0 (K.homology 0)).inv_hom_id
    (componentHomologyLinearEquiv K (cycleFromUnit K f).val)).trans
      (componentHomologyLinearEquiv_unit K f)

lemma zeroDegreeToSingle_unit (K : Complex A) [K.IsStrictlyLE 0] [K.IsStrictlyGE 0]
    (f : 𝟙_ (Complex A) ⟶ K) :
    f ≫ zeroDegreeToSingle K = singleUnit (K.homology 0) (unitClass K f) := by
  apply (unitCycleEquiv _).injective
  apply Subtype.ext
  apply ((ModuleCat.mono_iff_injective
    (singleObjXSelf (.up ℤ) 0 (K.homology 0)).hom).mp inferInstance)
  change singleValue (K.homology 0) (f ≫ zeroDegreeToSingle K) =
    singleValue (K.homology 0) (singleUnit (K.homology 0) (unitClass K f))
  rw [singleUnit_value, zeroDegreeToSingle_unit_value]

end SerrePositivity.EInfinity.HomologyZero

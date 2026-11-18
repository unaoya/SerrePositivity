module

public import SerrePositivity.HomologicalAlgebra.Complexes.HomologyZero.ZeroDegreeLinear
public import Mathlib.Algebra.Homology.Single

/-!
# 零次集中複体と元の H⁰ の単一複体の標準同型

概要：元のホモロジー類の写像を零次成分とする、実際の複体同型を構成する。
方針：零次成分の線形同型を single の入出射へ上げ、他次数を支持で消す。
規約：新しいホモロジーや加群構造を選ばない。
使われ方：零次集中 Com 代数から H⁰ の離散像への底の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomologyZero
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] (K : Complex A) [K.IsStrictlyLE 0] [K.IsStrictlyGE 0]

def zeroDegreeComponentIso : K.X 0 ≅ K.homology 0 :=
  (_root_.SerrePositivity.HomologyZero.componentHomologyLinearEquiv K).toModuleIso

def zeroDegreeToSingle : K ⟶ (single (ModuleCat A) (.up ℤ) 0).obj (K.homology 0) :=
  mkHomToSingle (_root_.SerrePositivity.HomologyZero.zeroDegreeComponentIso K).hom (by
    intro i hi
    exact (K.isZero_of_isStrictlyGE 0 i (by change i + 1 = 0 at hi; omega)).eq_of_src _ _)

def zeroDegreeFromSingle : (single (ModuleCat A) (.up ℤ) 0).obj (K.homology 0) ⟶ K :=
  mkHomFromSingle (_root_.SerrePositivity.HomologyZero.zeroDegreeComponentIso K).inv (by
    intro i hi
    exact (K.isZero_of_isStrictlyLE 0 i (by change 0 + 1 = i at hi; omega)).eq_of_tgt _ _)

def zeroDegreeHomologyIso : K ≅ (single (ModuleCat A) (.up ℤ) 0).obj (K.homology 0) where
  hom := _root_.SerrePositivity.HomologyZero.zeroDegreeToSingle K
  inv := _root_.SerrePositivity.HomologyZero.zeroDegreeFromSingle K
  hom_inv_id := by
    apply HomologicalComplex.hom_ext
    intro i
    rcases lt_trichotomy i 0 with hi | rfl | hi
    · exact (K.isZero_of_isStrictlyGE 0 i hi).eq_of_src _ _
    · simp only [_root_.SerrePositivity.HomologyZero.zeroDegreeToSingle, _root_.SerrePositivity.HomologyZero.zeroDegreeFromSingle, comp_f, mkHomToSingle_f,
        mkHomFromSingle_f, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, id_f]
    · exact (K.isZero_of_isStrictlyLE 0 i hi).eq_of_src _ _
  inv_hom_id := by
    apply HomologicalComplex.hom_ext
    intro i
    by_cases hi : i = 0
    · subst i
      simp only [_root_.SerrePositivity.HomologyZero.zeroDegreeToSingle, _root_.SerrePositivity.HomologyZero.zeroDegreeFromSingle, comp_f, mkHomToSingle_f,
        mkHomFromSingle_f, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, id_f]
    · exact (isZero_single_obj_X (.up ℤ) 0 (K.homology 0) i hi).eq_of_src _ _

lemma componentHomologyLinearEquiv_cycle (c : zeroCycles K) :
    _root_.SerrePositivity.HomologyZero.componentHomologyLinearEquiv K c.val = _root_.SerrePositivity.HomologyZero.classMap K c := rfl

lemma componentHomologyLinearEquiv_unit (f : 𝟙_ (Complex A) ⟶ K) :
    _root_.SerrePositivity.HomologyZero.componentHomologyLinearEquiv K (cycleFromUnit K f).val = _root_.SerrePositivity.HomologyZero.unitClass K f := rfl

end SerrePositivity.HomologyZero

module

public import SerrePositivity.CategoryTheory.BoundedHomotopy
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # 有界な有限射影複体とそのホモトピー圏

## 概要

可換環 `R` 上の、項が有限射影で有限個の次数の外で零となる複体（`strictlyPerfectComplex`）と、それを代表とするホモトピー圏の三角部分圏 `PerfectHomotopy R` を定める。零・シフト・写像錐・二項の直和で閉じること、包含の三角関手、具体的な複体を対象とする構成を与える。

## 方針

各次数の項を写像錐の項 `P^{q+1} ⊞ Q^q` や直和の項 `P^n × Q^n` と同一視し、有限性と射影性を線形同値で移す。三角部分圏の構造は `homotopyProperty_isTriangulatedClosed₃`（CategoryTheory/HomotopyProperty）による。

## 規約

台の条件や係数変更は扱わない（PerfectComplex/Perfect/HomotopyCategory）。

## 使われ方

PerfectComplex の全体、KTheory、DifferentialGraded/Perfect（DG の層の規則で PerfectComplex を import しないよう、ここに置く）。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

variable (R : Type u) [CommRing R]

/-- 項が有限射影で、有限個の次数の外で零となる複体。 -/
def strictlyPerfectComplex : ObjectProperty (CochainComplex (ModuleCat.{u} R) ℤ) :=
  fun P ↦ strictlyBoundedComplex (ModuleCat R) P ∧
    ∀ q, Module.Finite R (P.X q) ∧ Module.Projective R (P.X q)

/-- 有界有限射影複体を代表とするホモトピー圏の対象。 -/
def perfectHomotopyProperty : ObjectProperty (HomotopyCategory (ModuleCat.{u} R) (.up ℤ)) :=
  (strictlyPerfectComplex R).strictMap (HomotopyCategory.quotient _ _)

@[simp] lemma perfectHomotopyProperty_quotient (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    perfectHomotopyProperty R ((HomotopyCategory.quotient _ _).obj P) ↔
      strictlyPerfectComplex R P :=
  homotopyProperty_strictMap_quotient (strictlyPerfectComplex R) P

section
variable {R}

/-- The zero complex is strictly perfect over every commutative ring. -/
lemma strictlyPerfectComplex_zero :
    strictlyPerfectComplex R (0 : CochainComplex (ModuleCat.{u} R) ℤ) := by
  refine ⟨⟨0, 0, inferInstance, inferInstance⟩, fun i ↦ ?_⟩
  have hz : IsZero ((0 : CochainComplex (ModuleCat.{u} R) ℤ).X i) :=
    (HomologicalComplex.eval _ _ i).map_isZero
      (isZero_zero (CochainComplex (ModuleCat.{u} R) ℤ))
  have : Module.Free R ((0 : CochainComplex (ModuleCat.{u} R) ℤ).X i) :=
    isZero_moduleCat_free hz
  exact ⟨isZero_moduleCat_finite hz, Module.Projective.of_free⟩

/-- Integer shifts preserve strict perfectness. -/
lemma strictlyPerfectComplex_shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (n : ℤ) : strictlyPerfectComplex R (P⟦n⟧) := by
  exact ⟨strictlyBoundedComplex_shift _ hp.1 n, fun i ↦ hp.2 (i + n)⟩

end

instance : (perfectHomotopyProperty R).ContainsZero where
  exists_zero := ⟨(HomotopyCategory.quotient _ _).obj 0,
    Functor.map_isZero _ (isZero_zero _), by
      rw [perfectHomotopyProperty_quotient]
      exact strictlyPerfectComplex_zero⟩

instance : (perfectHomotopyProperty R).IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift X hX := by
        obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
        rw [perfectHomotopyProperty_quotient] at hX
        rw [ObjectProperty.prop_shift_iff, HomotopyCategory.shift_quotient_obj,
          perfectHomotopyProperty_quotient]
        exact strictlyPerfectComplex_shift hX n }

/-- 有限射影複体の写像錐は有限射影複体である。 -/
lemma strictlyPerfectComplex_mappingCone {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hP : strictlyPerfectComplex R P) (hQ : strictlyPerfectComplex R Q) :
    strictlyPerfectComplex R (CochainComplex.mappingCone f) := by
  refine ⟨strictlyBoundedComplex_mappingCone _ f hP.1 hQ.1, fun q ↦ ?_⟩
  have := (hP.2 (q + 1)).1
  have := (hP.2 (q + 1)).2
  have := (hQ.2 q).1
  have := (hQ.2 q).2
  let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl ≪≫
    ModuleCat.biprodIsoProd _ _).toLinearEquiv
  exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : (perfectHomotopyProperty R).IsTriangulatedClosed₃ :=
  homotopyProperty_isTriangulatedClosed₃ _ _ (perfectHomotopyProperty_quotient R)
    (fun f => strictlyPerfectComplex_mappingCone R f)

instance : (perfectHomotopyProperty R).IsTriangulated where
  toIsTriangulatedClosed₂ := .of_isTriangulatedClosed₃

/-- 有界有限射影複体のホモトピー圏。 -/
abbrev PerfectHomotopy := (perfectHomotopyProperty R).FullSubcategory

/-- 全ホモトピー圏への三角関手。 -/
abbrev perfectHomotopyInclusion : PerfectHomotopy R ⥤
    HomotopyCategory (ModuleCat.{u} R) (.up ℤ) := (perfectHomotopyProperty R).ι

/-- 具体的な有限射影複体をホモトピー圏の対象とする。 -/
def perfectHomotopyObj (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : strictlyPerfectComplex R P) : PerfectHomotopy R :=
  ⟨(HomotopyCategory.quotient _ _).obj P, (perfectHomotopyProperty_quotient R P).mpr hP⟩

section Biprod

variable {R}

set_option backward.isDefEq.respectTransparency false

attribute [local instance]
  CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBinaryProducts

def cochainBiprodXIsoProd (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (P ⊞ Q).X n ≅ ModuleCat.of R (P.X n × Q.X n) :=
  Functor.mapBiprod (HomologicalComplex.eval _ _ n) P Q ≪≫
    ModuleCat.biprodIsoProd (P.X n) (Q.X n)

lemma strictlyPerfectComplex_biprod {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    strictlyPerfectComplex R (P ⊞ Q) := by
  obtain ⟨a, b, ha, hb⟩ := hp.1
  obtain ⟨c, d, hc, hd⟩ := hq.1
  have hz : ∀ n, IsZero (P.X n) → IsZero (Q.X n) → IsZero ((P ⊞ Q).X n) := by
    intro n hn hn'
    have := ModuleCat.subsingleton_of_isZero hn
    have := ModuleCat.subsingleton_of_isZero hn'
    exact (ModuleCat.isZero_of_subsingleton (ModuleCat.of R (P.X n × Q.X n))).of_iso
      (cochainBiprodXIsoProd P Q n)
  refine ⟨⟨min a c, max b d, ?_, ?_⟩, fun n => ?_⟩
  · exact ((P ⊞ Q).isStrictlyGE_iff _).mpr fun n hn => hz n
      (P.isZero_of_isStrictlyGE a n (lt_of_lt_of_le hn (min_le_left _ _)))
      (Q.isZero_of_isStrictlyGE c n (lt_of_lt_of_le hn (min_le_right _ _)))
  · exact ((P ⊞ Q).isStrictlyLE_iff _).mpr fun n hn => hz n
      (P.isZero_of_isStrictlyLE b n (lt_of_le_of_lt (le_max_left _ _) hn))
      (Q.isZero_of_isStrictlyLE d n (lt_of_le_of_lt (le_max_right _ _) hn))
  · have := (hp.2 n).1
    have := (hq.2 n).1
    have := (hp.2 n).2
    have := (hq.2 n).2
    let e := (cochainBiprodXIsoProd P Q n).toLinearEquiv
    exact ⟨Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective,
      Module.Projective.of_equiv' e.symm⟩

end Biprod

end SerrePositivity

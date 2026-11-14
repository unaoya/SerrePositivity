module

public import SerrePositivity.AlgebraicGeometry.CechRefinementCone
public import SerrePositivity.AlgebraicGeometry.CechHomologyCycleCriterion
public import Mathlib.Algebra.Homology.QuasiIso

/-!
概要：refinement map の cone の完全性から、各次数の Čech H の同型性を導く。
方針：cone のサイクルの前像を用いて、H の全射性と単射性をサイクルで示す。
規約：加群の複体の一般論。原典の層コホモロジーとの比較を仮定しない。
使われ方：B1 が与える二重図式の零番の行の完全性を、共通細分の H の比較へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R : Type u} [CommRing R]
variable (A B : CochainComplex (ModuleCat.{u} R) ℕ) (f : A ⟶ B)
variable (hzero : ∀ x : cechRefinementConeTerm A B 0,
  cechRefinementConeDifferential A B f 0 x = 0 → x = 0)
variable (hbound : ∀ n (x : cechRefinementConeTerm A B (n + 1)),
  cechRefinementConeDifferential A B f (n + 1) x = 0 →
    ∃ y, cechRefinementConeDifferential A B f n y = x)
include hzero hbound

/-- 自然数添字の cone が完全なら、元の射は各次数で quasi-isomorphism。 -/
theorem cechRefinementCone_quasiIsoAt (q : ℕ) : QuasiIsoAt f q := by
  cases q with
  | zero =>
    rw [CochainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff]
    apply cechHomologyMap_isIso_of_cycles (A.sc' 0 0 1) (B.sc' 0 0 1)
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ) 0 0 1).map f)
    · intro b hb
      change B.X 0 at b
      change (B.d 0 1).hom b = 0 at hb
      have hc : cechRefinementConeDifferential A B f 1 (b, 0) = 0 := by
        change ((B.d 0 1).hom b + (f.f 1).hom 0, -(A.d 1 2).hom 0) = (0, 0)
        simp only [hb, map_zero, add_zero, neg_zero]
      obtain ⟨a, ha⟩ := hbound 0 _ hc
      have hfa : (f.f 0).hom a = b := congrArg Prod.fst ha
      have hda : (A.d 0 1).hom a = 0 := neg_eq_zero.mp (congrArg Prod.snd ha)
      refine ⟨a, 0, hda, ?_⟩
      change (f.f 0).hom a = b + (B.d 0 0).hom 0
      simpa only [map_zero, add_zero] using hfa
    · intro a ha hb
      change (A.d 0 1).hom a = 0 at ha
      obtain ⟨b, hb⟩ := hb
      change (B.d 0 0).hom b = (f.f 0).hom a at hb
      have hfzero : (f.f 0).hom a = 0 := by
        simpa only [B.shape 0 0 (by simp), ModuleCat.hom_zero, LinearMap.zero_apply] using hb.symm
      have hazero : a = 0 := hzero a (by
        change ((f.f 0).hom a, -(A.d 0 1).hom a) = (0, 0)
        rw [hfzero, ha, neg_zero])
      refine ⟨0, ?_⟩
      change (A.d 0 0).hom 0 = a
      rw [map_zero, hazero]
  | succ n =>
    rw [quasiIsoAt_iff' f n (n + 1) (n + 2)
      (ComplexShape.prev_eq' (.up ℕ) (by rfl)) (ComplexShape.next_eq' (.up ℕ) (by rfl)),
      ShortComplex.quasiIso_iff]
    apply cechHomologyMap_isIso_of_cycles (A.sc' n (n + 1) (n + 2)) (B.sc' n (n + 1) (n + 2))
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ) n (n + 1) (n + 2)).map f)
    · intro b hb
      change B.X (n + 1) at b
      change (B.d (n + 1) (n + 2)).hom b = 0 at hb
      have hc : cechRefinementConeDifferential A B f (n + 2) (b, 0) = 0 := by
        change ((B.d (n + 1) (n + 2)).hom b + (f.f (n + 2)).hom 0,
          -(A.d (n + 2) (n + 3)).hom 0) = (0, 0)
        simp only [hb, map_zero, add_zero, neg_zero]
      obtain ⟨y, hy⟩ := hbound (n + 1) _ hc
      have hfirst : (B.d n (n + 1)).hom y.1 + (f.f (n + 1)).hom y.2 = b :=
        congrArg Prod.fst hy
      have hda : (A.d (n + 1) (n + 2)).hom y.2 = 0 :=
        neg_eq_zero.mp (congrArg Prod.snd hy)
      refine ⟨y.2, -y.1, hda, ?_⟩
      change (f.f (n + 1)).hom y.2 = b + (B.d n (n + 1)).hom (-y.1)
      rw [map_neg, ← hfirst]
      abel
    · intro a ha hb
      change (A.d (n + 1) (n + 2)).hom a = 0 at ha
      obtain ⟨b, hb⟩ := hb
      change (B.d n (n + 1)).hom b = (f.f (n + 1)).hom a at hb
      have hc : cechRefinementConeDifferential A B f (n + 1) (-b, a) = 0 := by
        change ((B.d n (n + 1)).hom (-b) + (f.f (n + 1)).hom a,
          -(A.d (n + 1) (n + 2)).hom a) = (0, 0)
        rw [map_neg, hb, neg_add_cancel, ha, neg_zero]
      obtain ⟨y, hy⟩ := hbound n _ hc
      cases n with
      | zero =>
        refine ⟨-y, ?_⟩
        change (A.d 0 1).hom (-y) = a
        rw [map_neg]
        exact congrArg Prod.snd hy
      | succ n =>
        refine ⟨-y.2, ?_⟩
        change (A.d (n + 1) (n + 2)).hom (-y.2) = a
        rw [map_neg]
        exact congrArg Prod.snd hy

/-- cone の完全性が与える、元の複体の各次数の H の同型性。 -/
theorem cechRefinementCone_homologyMap_isIso (q : ℕ) :
    IsIso (HomologicalComplex.homologyMap f q) :=
  (quasiIsoAt_iff_isIso_homologyMap f q).mp
    (cechRefinementCone_quasiIsoAt A B f hzero hbound q)

end SerrePositivity.AlgebraicGeometry

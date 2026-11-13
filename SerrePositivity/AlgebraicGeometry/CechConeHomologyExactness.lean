module

public import SerrePositivity.AlgebraicGeometry.CechRefinementCone
public import SerrePositivity.AlgebraicGeometry.CechHomologyCycleLifting

/-!
概要：H⁰ の全射性と正次数の H の同型性から、自然数添字の cone の正次数の完全性を得る。
方針：サイクルの第二成分を境界へ戻し、残った第一成分を H の全射性で持ち上げる。
規約：明示的な cone の微分を用い、各次数の短複体は通常の H を計算するもの。
使われ方：F6 と F7 を F8 の明示的な増大全複体へ接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable (A B : CochainComplex (ModuleCat.{u} R) ℕ) (f : A ⟶ B)

/-- H⁰ が全射、正次数の H が全単射なら cone の各正次数サイクルは境界。 -/
theorem cechRefinementCone_cycle_boundary_of_homology
    (hzero : Function.Surjective (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ) 0 0 1).map f)).hom)
    (hpos : ∀ n, Function.Bijective (ShortComplex.homologyMap
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
        n (n + 1) (n + 2)).map f)).hom)
    (n : ℕ) (x : cechRefinementConeTerm A B (n + 1))
    (hx : cechRefinementConeDifferential A B f (n + 1) x = 0) :
    ∃ y, cechRefinementConeDifferential A B f n y = x := by
  have hf (i : ℕ) (a : A.X i) :
      (B.d i (i + 1)).hom ((f.f i).hom a) =
        (f.f (i + 1)).hom ((A.d i (i + 1)).hom a) := by
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using
      congrArg (fun g ↦ g.hom a) (f.comm i (i + 1))
  cases n with
  | zero =>
    change ((B.d 0 1).hom x.1 + (f.f 1).hom x.2,
      -(A.d 1 2).hom x.2) = (0, 0) at hx
    have ha : (A.d 1 2).hom x.2 = 0 := neg_eq_zero.mp (congrArg Prod.snd hx)
    have hb : (B.d 0 1).hom (-x.1) = (f.f 1).hom x.2 := by
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_right (congrArg Prod.fst hx)).symm
    obtain ⟨y, hy⟩ := cechCycles_boundary_of_homology_injective
      (A.sc' 0 1 2) (B.sc' 0 1 2)
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ) 0 1 2).map f)
      (hpos 0).1 x.2 ha ⟨-x.1, hb⟩
    change A.X 0 at y
    change (A.d 0 1).hom y = x.2 at hy
    have hc : (B.d 0 1).hom (x.1 + (f.f 0).hom y) = 0 := by
      rw [map_add, hf, hy]
      exact congrArg Prod.fst hx
    obtain ⟨z, w, hz, he⟩ := cechCycles_lift_of_homology_surjective
      (A.sc' 0 0 1) (B.sc' 0 0 1)
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ) 0 0 1).map f)
      hzero _ hc
    change A.X 0 at z
    change B.X 0 at w
    change (f.f 0).hom z = x.1 + (f.f 0).hom y + (B.d 0 0).hom w at he
    have he' : (f.f 0).hom z = x.1 + (f.f 0).hom y := by
      simpa only [B.shape 0 0 (by simp), ModuleCat.hom_zero, LinearMap.zero_apply,
        add_zero] using he
    refine ⟨z - y, ?_⟩
    apply Prod.ext
    · change (f.f 0).hom (z - y) = x.1
      rw [map_sub, he', add_sub_cancel_right]
    · change -(A.d 0 1).hom (z - y) = x.2
      change (A.d 0 1).hom z = 0 at hz
      rw [map_sub, hz, zero_sub, neg_neg, hy]
  | succ n =>
    change ((B.d (n + 1) (n + 2)).hom x.1 + (f.f (n + 2)).hom x.2,
      -(A.d (n + 2) (n + 3)).hom x.2) = (0, 0) at hx
    have ha : (A.d (n + 2) (n + 3)).hom x.2 = 0 :=
      neg_eq_zero.mp (congrArg Prod.snd hx)
    have hb : (B.d (n + 1) (n + 2)).hom (-x.1) = (f.f (n + 2)).hom x.2 := by
      rw [map_neg]
      exact (eq_neg_of_add_eq_zero_right (congrArg Prod.fst hx)).symm
    obtain ⟨y, hy⟩ := cechCycles_boundary_of_homology_injective
      (A.sc' (n + 1) (n + 2) (n + 3)) (B.sc' (n + 1) (n + 2) (n + 3))
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
        (n + 1) (n + 2) (n + 3)).map f)
      (hpos (n + 1)).1 x.2 ha ⟨-x.1, hb⟩
    change A.X (n + 1) at y
    change (A.d (n + 1) (n + 2)).hom y = x.2 at hy
    have hc : (B.d (n + 1) (n + 2)).hom (x.1 + (f.f (n + 1)).hom y) = 0 := by
      rw [map_add, hf, hy]
      exact congrArg Prod.fst hx
    obtain ⟨z, w, hz, he⟩ := cechCycles_lift_of_homology_surjective
      (A.sc' n (n + 1) (n + 2)) (B.sc' n (n + 1) (n + 2))
      ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R) (.up ℕ)
        n (n + 1) (n + 2)).map f) (hpos n).2 _ hc
    change A.X (n + 1) at z
    change B.X n at w
    refine ⟨(-w, z - y), ?_⟩
    apply Prod.ext
    · change (B.d n (n + 1)).hom (-w) + (f.f (n + 1)).hom (z - y) = x.1
      change (f.f (n + 1)).hom z =
        x.1 + (f.f (n + 1)).hom y + (B.d n (n + 1)).hom w at he
      rw [map_neg, map_sub, he]
      abel
    · change -(A.d (n + 1) (n + 2)).hom (z - y) = x.2
      change (A.d (n + 1) (n + 2)).hom z = 0 at hz
      rw [map_sub, hz, zero_sub, neg_neg, hy]

end SerrePositivity.AlgebraicGeometry

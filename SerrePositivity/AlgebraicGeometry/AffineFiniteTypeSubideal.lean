module

public import SerrePositivity.AlgebraicGeometry.FiniteIdealMapApproximation
public import SerrePositivity.AlgebraicGeometry.FiniteTypeIdealSheafLocality

/-!
概要：アフィン基底の有限個の開の切断を、一つの有限型部分イデアル層に含める。
方針：全体切断イデアルの像について有限選択し、有限和を取って戻す。
規約：基底の Noether 性は不要。
使われ方：Stacks 01PF、有限型部分イデアルの大域延長のアフィン部分。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u

set_option backward.isDefEq.respectTransparency false in
/-- アフィン基底上の有限個のアフィン開の切断を、有限型な部分イデアル層へ含める。 -/
theorem exists_finiteType_subideal_containing_affine_sections_of_isAffine
    {X : Scheme.{u}} [IsAffine X] (K : X.IdealSheafData)
    {ι : Type u} [Finite ι] (U : ι → X.affineOpens)
    (s : ∀ i, Finset Γ(X, (U i).1))
    (hs : ∀ i x, x ∈ s i → x ∈ K.ideal (U i)) :
    ∃ J : X.IdealSheafData, J ≤ K ∧ IsFiniteTypeIdealSheaf J ∧
      ∀ i x, x ∈ s i → x ∈ J.ideal (U i) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  let T : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let I := K.ideal T
  let f (i : ι) : Γ(X, ⊤) →+* Γ(X, (U i).1) :=
    (X.presheaf.map (homOfLE (show (U i).1 ≤ ⊤ from le_top)).op).hom
  have hmap (i : ι) : I.map (f i) = K.ideal (U i) := K.map_ideal (show (U i).1 ≤ T.1 from le_top)
  have hSi (i : ι) : ∀ x ∈ s i, x ∈ I.map (f i) := by
    intro x hx
    rw [hmap]
    exact hs i x hx
  choose L hL hLI hsL using fun i ↦
    exists_fg_subideal_map_contains_finset (f i) I (s i) (hSi i)
  let N := Finset.univ.sup L
  have hN : N.FG := Submodule.fg_finset_sup Finset.univ L (fun i _ ↦ hL i)
  have hNI : N ≤ I := Finset.sup_le fun i _ ↦ hLI i
  let E := Scheme.IdealSheafData.equivOfIsAffine (X := X)
  let J := E.symm N
  have htop : J.ideal T = N := E.apply_symm_apply N
  refine ⟨J, ?_, ?_, ?_⟩
  · apply Scheme.IdealSheafData.le_of_isAffine
    change J.ideal T ≤ I
    rw [htop]
    exact hNI
  · apply isFiniteTypeIdealSheaf_of_fg_top J
    change (J.ideal T).FG
    rw [htop]
    exact hN
  · intro i x hx
    have hle : L i ≤ N := Finset.le_sup (Finset.mem_univ i)
    have hxN : x ∈ N.map (f i) := Ideal.map_mono hle (hsL i x hx)
    have heq : N.map (f i) = J.ideal (U i) := by
      rw [← htop]
      exact J.map_ideal (show (U i).1 ≤ T.1 from le_top)
    exact heq ▸ hxN

end SerrePositivity.AlgebraicGeometry

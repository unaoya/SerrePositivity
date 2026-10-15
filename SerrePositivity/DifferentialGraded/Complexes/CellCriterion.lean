module
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import SerrePositivity.DifferentialGraded.Complexes.AcyclicCone
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-! # sphere→disk の生成元方程式はconeのacyclic性を検出する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A]

/-- 複体射の境界を指定しながら生成元をliftする条件。 -/
def complexBoundaryLiftAt {K L : Complex A} (f : K ⟶ L) (n : ℤ) : Prop :=
  ∀ z : complexCycles A K (n + 1), ∀ y : L.X n,
    f.f (n + 1) z.val = L.d n (n + 1) y →
      ∃ t : K.X n, K.d n (n + 1) t = z.val ∧ f.f n t = y

/-- coneの要素は二つの標準射影で判定できる。 -/
lemma complexCone_element_ext {K L : Complex A} (f : K ⟶ L) (i : ℤ)
    {z w : (mappingCone f).X i}
    (h₁ : homotopyCofiber.fstX f i (i + 1) rfl z = homotopyCofiber.fstX f i (i + 1) rfl w)
    (h₂ : homotopyCofiber.sndX f i z = homotopyCofiber.sndX f i w) : z = w := by
  have hm : moduleElementMap A _ z = moduleElementMap A _ w := by
    apply homotopyCofiber.ext_to_X f i (i + 1) rfl
    · apply (moduleElementEquiv A (K.X (i + 1))).injective
      change homotopyCofiber.fstX f i (i + 1) rfl ((1 : A) • z) =
        homotopyCofiber.fstX f i (i + 1) rfl ((1 : A) • w)
      simpa only [one_smul] using h₁
    · apply (moduleElementEquiv A (L.X i)).injective
      change homotopyCofiber.sndX f i ((1 : A) • z) = homotopyCofiber.sndX f i ((1 : A) • w)
      simpa only [one_smul] using h₂
  have he := congrArg (fun k => k (1 : A)) hm
  change (1 : A) • z = (1 : A) • w at he
  simpa only [one_smul] using he

/-- 全整数次数で境界cellをliftできる複体射は準同型。 -/
lemma complex_quasiIso_of_boundary_lifting {K L : Complex A} (f : K ⟶ L)
    (h : ∀ n : ℤ, complexBoundaryLiftAt A f n) : QuasiIso f := by
  apply (complex_quasiIso_iff_acyclic_cone A f).2
  intro i
  apply (HomologicalComplex.exactAt_iff' (K := mappingCone f) (i := i - 1) (j := i)
    (k := i + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : (mappingCone f).X i, (mappingCone f).d i (i + 1) z = 0 →
    ∃ t : (mappingCone f).X (i - 1), (mappingCone f).d (i - 1) i t = z
  intro z hz
  let a := homotopyCofiber.fstX f i (i + 1) rfl z
  let b := homotopyCofiber.sndX f i z
  have ha : K.d (i + 1) (i + 1 + 1) a = 0 := by
    have hc := congrArg (fun k => k z) (homotopyCofiber.d_fstX f i (i + 1) (i + 1 + 1) rfl rfl)
    change homotopyCofiber.fstX f (i + 1) (i + 1 + 1) rfl
      ((mappingCone f).d i (i + 1) z) = -K.d (i + 1) (i + 1 + 1) a at hc
    rw [hz, map_zero] at hc
    exact neg_eq_zero.mp hc.symm
  have hab : f.f (i + 1) a + L.d i (i + 1) b = 0 := by
    have hc := congrArg (fun k => k z) (homotopyCofiber.d_sndX f i (i + 1) rfl)
    change homotopyCofiber.sndX f (i + 1) ((mappingCone f).d i (i + 1) z) =
      f.f (i + 1) a + L.d i (i + 1) b at hc
    rw [hz, map_zero] at hc
    exact hc.symm
  have hc : f.f (i + 1) a = L.d i (i + 1) (-b) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_left hab
  obtain ⟨t, ht, hf⟩ := h i ⟨a, ha⟩ (-b) hc
  let e := -homotopyCofiber.inlX f i (i - 1) (show (ComplexShape.up ℤ).Rel (i - 1) i by simp) t
  refine ⟨e, ?_⟩
  apply complexCone_element_ext A f i
  · have hd := congrArg (fun k => k e)
      (homotopyCofiber.d_fstX f (i - 1) i (i + 1) (by simp) rfl)
    change homotopyCofiber.fstX f i (i + 1) rfl ((mappingCone f).d (i - 1) i e) =
      -K.d i (i + 1) (homotopyCofiber.fstX f (i - 1) i (by simp) e) at hd
    rw [hd]
    have he : homotopyCofiber.fstX f (i - 1) i (by simp) e = -t := by
      dsimp [e]
      rw [map_neg, ← ModuleCat.comp_apply, homotopyCofiber.inlX_fstX, ModuleCat.id_apply]
    rw [he, map_neg, neg_neg]
    exact ht
  · have hd := congrArg (fun k => k e)
      (homotopyCofiber.d_sndX f (i - 1) i (by simp))
    change homotopyCofiber.sndX f i ((mappingCone f).d (i - 1) i e) =
      f.f i (homotopyCofiber.fstX f (i - 1) i (by simp) e) +
        L.d (i - 1) i (homotopyCofiber.sndX f (i - 1) e) at hd
    rw [hd]
    have he₁ : homotopyCofiber.fstX f (i - 1) i (by simp) e = -t := by
      dsimp [e]
      rw [map_neg, ← ModuleCat.comp_apply, homotopyCofiber.inlX_fstX, ModuleCat.id_apply]
    have he₂ : homotopyCofiber.sndX f (i - 1) e = 0 := by
      dsimp [e]
      rw [map_neg, ← ModuleCat.comp_apply, homotopyCofiber.inlX_sndX]
      exact neg_zero
    rw [he₁, he₂, map_zero, add_zero, map_neg, hf, neg_neg]

/-- 次数ごと全射な準同型なら、境界を保つ生成元の同時liftが存在する。 -/
lemma complex_boundary_lifting_of_surjective_quasiIso {K L : Complex A} (f : K ⟶ L)
    (hs : ∀ i : ℤ, Function.Surjective (f.f i)) (hq : QuasiIso f) (n : ℤ) :
    complexBoundaryLiftAt A f n := by
  intro z y hy
  let c := homotopyCofiber.inlX f (n + 1) n rfl z.val - homotopyCofiber.inrX f n y
  have hc₁ : homotopyCofiber.fstX f n (n + 1) rfl c = z.val := by
    dsimp [c]
    rw [map_sub, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      homotopyCofiber.inlX_fstX, homotopyCofiber.inrX_fstX, ModuleCat.id_apply]
    exact sub_zero z.val
  have hc₂ : homotopyCofiber.sndX f n c = -y := by
    dsimp [c]
    rw [map_sub, ← ModuleCat.comp_apply, ← ModuleCat.comp_apply,
      homotopyCofiber.inlX_sndX, homotopyCofiber.inrX_sndX, ModuleCat.id_apply]
    exact zero_sub y
  have hc : (mappingCone f).d n (n + 1) c = 0 := by
    apply complexCone_element_ext A f (n + 1)
    · rw [map_zero]
      have hd := congrArg (fun k => k c)
        (homotopyCofiber.d_fstX f n (n + 1) (n + 1 + 1) rfl rfl)
      change homotopyCofiber.fstX f (n + 1) (n + 1 + 1) rfl
        ((mappingCone f).d n (n + 1) c) =
          -K.d (n + 1) (n + 1 + 1) (homotopyCofiber.fstX f n (n + 1) rfl c) at hd
      rw [hd, hc₁, z.property, neg_zero]
    · rw [map_zero]
      have hd := congrArg (fun k => k c) (homotopyCofiber.d_sndX f n (n + 1) rfl)
      change homotopyCofiber.sndX f (n + 1) ((mappingCone f).d n (n + 1) c) =
        f.f (n + 1) (homotopyCofiber.fstX f n (n + 1) rfl c) +
          L.d n (n + 1) (homotopyCofiber.sndX f n c) at hd
      rw [hd, hc₁, hc₂, map_neg, hy, add_neg_cancel]
  have he := (complex_quasiIso_iff_acyclic_cone A f).1 hq n
  rw [HomologicalComplex.exactAt_iff' (K := mappingCone f) (i := n - 1) (j := n)
    (k := n + 1) (by simp) (by simp), ShortComplex.moduleCat_exact_iff] at he
  change ∀ v : (mappingCone f).X n, (mappingCone f).d n (n + 1) v = 0 →
    ∃ e : (mappingCone f).X (n - 1), (mappingCone f).d (n - 1) n e = v at he
  obtain ⟨e, he⟩ := he c hc
  let u := homotopyCofiber.fstX f (n - 1) n (by simp) e
  let v := homotopyCofiber.sndX f (n - 1) e
  have hu : -K.d n (n + 1) u = z.val := by
    have hd := congrArg (fun k => k e)
      (homotopyCofiber.d_fstX f (n - 1) n (n + 1) (by simp) rfl)
    change homotopyCofiber.fstX f n (n + 1) rfl ((mappingCone f).d (n - 1) n e) =
      -K.d n (n + 1) u at hd
    rw [he, hc₁] at hd
    exact hd.symm
  have huv : f.f n u + L.d (n - 1) n v = -y := by
    have hd := congrArg (fun k => k e) (homotopyCofiber.d_sndX f (n - 1) n (by simp))
    change homotopyCofiber.sndX f n ((mappingCone f).d (n - 1) n e) =
      f.f n u + L.d (n - 1) n v at hd
    rw [he, hc₂] at hd
    exact hd.symm
  obtain ⟨q, hq⟩ := hs (n - 1) v
  refine ⟨-u - K.d (n - 1) n q, ?_, ?_⟩
  · have hd := congrArg (fun k => k q) (K.d_comp_d (n - 1) n (n + 1))
    change K.d n (n + 1) (K.d (n - 1) n q) = 0 at hd
    rw [map_sub, map_neg, hd, sub_zero]
    exact hu
  · have hd := congrArg (fun k => k q) (f.comm (n - 1) n)
    change L.d (n - 1) n (f.f (n - 1) q) = f.f n (K.d (n - 1) n q) at hd
    rw [hq] at hd
    rw [map_sub, map_neg, ← hd]
    have hv := congrArg Neg.neg huv
    simpa only [neg_add, neg_neg, sub_eq_add_neg] using hv

end SerrePositivity.DifferentialGraded

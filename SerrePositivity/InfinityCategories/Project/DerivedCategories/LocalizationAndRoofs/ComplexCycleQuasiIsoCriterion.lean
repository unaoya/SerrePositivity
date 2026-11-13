module
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct
public import SerrePositivity.DifferentialGraded.Complexes.TensorShift
/-!
概要：閉 cochain の像の持ち上げと境界の反映から Hom 複体の準同型性を検出する。
方針：元の cycle と境界原始元を保持した商の比較を使う。
規約：全次数の検査を省かない。使われ方：一般 Morita の全 Hom 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory HomologicalComplex CochainComplex DifferentialGraded
variable (R : Type u) [CommRing R]
/-- 元の閉 cochain と境界原始元による検出。 -/
lemma complexQuasiIso_of_cycle_lift_boundary_reflect {K L : Complex R} (f : K ⟶ L)
    (hs : ∀ q : ℤ, ∀ z : L.X (q + 1), L.d (q + 1) (q + 1 + 1) z = 0 →
      ∃ a : K.X (q + 1), K.d (q + 1) (q + 1 + 1) a = 0 ∧
        ∃ b : L.X q, L.d q (q + 1) b = z - f.f (q + 1) a)
    (hi : ∀ q : ℤ, ∀ a : K.X (q + 1), K.d (q + 1) (q + 1 + 1) a = 0 →
      ∀ b : L.X q, L.d q (q + 1) b = f.f (q + 1) a →
        ∃ t : K.X q, K.d q (q + 1) t = a) : QuasiIso f := by
  apply (complex_quasiIso_iff_acyclic_cone R f).2
  intro i
  obtain ⟨q, hq⟩ : ∃ q : ℤ, i = q + 1 := ⟨i - 1, by omega⟩
  subst i
  apply (HomologicalComplex.exactAt_iff' (K := mappingCone f) (i := q) (j := q + 1)
    (k := q + 1 + 1) (by simp) (by simp)).2
  rw [ShortComplex.moduleCat_exact_iff]
  change ∀ z : (mappingCone f).X (q + 1), (mappingCone f).d (q + 1) (q + 1 + 1) z = 0 →
    ∃ e : (mappingCone f).X q, (mappingCone f).d q (q + 1) e = z
  intro z hz
  let a := (mappingCone.fst f).val.v (q + 1) (q + 1 + 1) rfl z
  let b := (mappingCone.snd f).v (q + 1) (q + 1) (add_zero _) z
  have ha : K.d (q + 1 + 1) (q + 1 + 1 + 1) a = 0 := by
    have h := complexCone_d_fst R f (q + 1) z
    rw [hz, map_zero] at h
    exact neg_eq_zero.mp h.symm
  have hab : f.f (q + 1 + 1) a + L.d (q + 1) (q + 1 + 1) b = 0 := by
    have h := complexCone_d_snd R f (q + 1) z
    rw [hz, map_zero] at h
    exact h.symm
  have hb : L.d (q + 1) (q + 1 + 1) (-b) = f.f (q + 1 + 1) a := by
    rw [map_neg]
    exact (eq_neg_of_add_eq_zero_left hab).symm
  obtain ⟨t, ht⟩ := hi (q + 1) a ha (-b) hb
  let c := b + f.f (q + 1) t
  have hc : L.d (q + 1) (q + 1 + 1) c = 0 := by
    have h := ConcreteCategory.congr_hom (f.comm (q + 1) (q + 1 + 1)) t
    change L.d (q + 1) (q + 1 + 1) (f.f (q + 1) t) =
      f.f (q + 1 + 1) (K.d (q + 1) (q + 1 + 1) t) at h
    dsimp only [c]
    rw [map_add, h, ht]
    exact (add_comm _ _).trans hab
  obtain ⟨a', ha', b', hb'⟩ := hs q c hc
  let e := complexConeElementMk R f q (-t + a') b'
  refine ⟨e, ?_⟩
  apply complexConeElement_ext R f (q + 1)
  · change _ = a
    rw [complexCone_d_fst, complexConeElementMk_fst, map_add, map_neg, ht, ha', add_zero, neg_neg]
  · change _ = b
    rw [complexCone_d_snd, complexConeElementMk_fst, complexConeElementMk_snd,
      map_add, map_neg, hb']
    dsimp only [c]
    abel
end SerrePositivity.InfinityCategories.Project.DerivedCategories

module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComplex
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：有限交叉の係数図式の写像を Čech 複体の写像へ送る。
方針：各タプルの成分に自然変換を適用する。
規約：被覆の添字集合は固定し、係数図式だけを変える。
使われ方：Laurent 表示の同型と斉次表示の短完全列を Čech 複体へ移す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

variable {R : Type*} [CommRing R]
variable {ι : Type*} [DecidableEq ι]
variable {D E F : Finset ι ⥤ ModuleCat R}

omit [DecidableEq ι] in
private theorem cechCoefficientMap_restrict (η : D ⟶ E) {s t : Finset ι} (h : s ⊆ t)
    (a : D.obj s) :
    (η.app t).hom ((D.map (homOfLE h)).hom a) =
      (E.map (homOfLE h)).hom ((η.app s).hom a) := by
  have he := congrArg (fun f : D.obj s ⟶ E.obj t ↦ f.hom a) (η.naturality (homOfLE h))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using he

/-- 全タプル版の各項の係数を自然変換で移す。 -/
def fullCechCochainsMap (η : D ⟶ E) (k : ℕ) : FullCechCochains D k →ₗ[R] FullCechCochains E k :=
  LinearMap.pi fun t ↦ (η.app (cechTupleSupport t)).hom.comp (LinearMap.proj t)

/-- 係数の自然変換は全タプル版の余境界と可換。 -/
theorem fullCechCochainsMap_comp_differential (η : D ⟶ E) (k : ℕ) :
    (fullCechCochainsMap η (k + 1)).comp (fullCechDifferential D k) =
      (fullCechDifferential E k).comp (fullCechCochainsMap η k) := by
  apply LinearMap.ext
  intro a
  funext t
  change (η.app (cechTupleSupport t)).hom (fullCechDifferential D k a t) =
    fullCechDifferential E k (fullCechCochainsMap η k a) t
  simp only [fullCechDifferential_apply, map_sum, map_zsmul, fullCechCochainsMap,
    LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [cechCoefficientMap_restrict η]

/-- 係数図式の自然変換が誘導する全タプル版 Čech のコチェイン写像。 -/
def fullCechComplexMap (η : D ⟶ E) : fullCechComplex D ⟶ fullCechComplex E :=
  CochainComplex.ofHom (fun q ↦ ModuleCat.ofHom (fullCechCochainsMap η (q + 1))) (by
    intro q
    change ModuleCat.ofHom (fullCechCochainsMap η (q + 1)) ≫ (fullCechComplex E).d q (q + 1) =
      (fullCechComplex D).d q (q + 1) ≫ ModuleCat.ofHom (fullCechCochainsMap η (q + 2))
    simp only [fullCechComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      (fullCechCochainsMap_comp_differential η (q + 1)).symm)

/-- 全タプル Čech 複体を係数図式の関手とする。 -/
def fullCechComplexFunctor : (Finset ι ⥤ ModuleCat R) ⥤ CochainComplex (ModuleCat R) ℕ where
  obj := fullCechComplex
  map := fullCechComplexMap
  map_id _ := by
    ext q a
    rfl
  map_comp _ _ := by
    ext q a
    rfl

section Ordered

variable [LinearOrder ι]

/-- 狭義増加版の各項の係数を自然変換で移す。 -/
def orderedCechCochainsMap (η : D ⟶ E) (k : ℕ) :
    OrderedCechCochains D k →ₗ[R] OrderedCechCochains E k :=
  LinearMap.pi fun t ↦ (η.app (cechTupleSupport t.val)).hom.comp (LinearMap.proj t)

/-- 係数の自然変換は狭義増加版の余境界と可換。 -/
theorem orderedCechCochainsMap_comp_differential (η : D ⟶ E) (k : ℕ) :
    (orderedCechCochainsMap η (k + 1)).comp (orderedCechDifferential D k) =
      (orderedCechDifferential E k).comp (orderedCechCochainsMap η k) := by
  apply LinearMap.ext
  intro a
  funext t
  simp only [orderedCechCochainsMap, orderedCechDifferential, LinearMap.comp_apply,
    LinearMap.pi_apply, LinearMap.proj_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  rw [cechCoefficientMap_restrict η]

/-- 係数図式の自然変換が誘導する狭義増加版 Čech のコチェイン写像。 -/
def orderedCechComplexMap (η : D ⟶ E) : orderedCechComplex D ⟶ orderedCechComplex E :=
  CochainComplex.ofHom (fun q ↦ ModuleCat.ofHom (orderedCechCochainsMap η (q + 1))) (by
    intro q
    change ModuleCat.ofHom (orderedCechCochainsMap η (q + 1)) ≫ (orderedCechComplex E).d q (q + 1) =
      (orderedCechComplex D).d q (q + 1) ≫ ModuleCat.ofHom (orderedCechCochainsMap η (q + 2))
    simp only [orderedCechComplex, CochainComplex.of_d]
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
      (orderedCechCochainsMap_comp_differential η (q + 1)).symm)

/-- 狭義増加 Čech 複体を係数図式の関手とする。 -/
def orderedCechComplexFunctor : (Finset ι ⥤ ModuleCat R) ⥤ CochainComplex (ModuleCat R) ℕ where
  obj := orderedCechComplex
  map := orderedCechComplexMap
  map_id _ := by
    ext q a
    rfl
  map_comp _ _ := by
    ext q a
    rfl

instance : (orderedCechComplexFunctor (R := R) (ι := ι)).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext q a
    rfl

/-- 狭義増加タプルでの成分射影は係数図式の自然変換と可換。 -/
def fullCechComplexRestrictOrderedNatTrans :
    fullCechComplexFunctor (R := R) (ι := ι) ⟶ orderedCechComplexFunctor where
  app := fullCechComplexRestrictOrdered
  naturality _ _ _ := by
    ext q a
    rfl

/-- 各交叉の係数列が短完全なら、狭義増加 Čech 複体の列も短完全。 -/
theorem orderedCechComplex_shortExact (f : D ⟶ E) (g : E ⟶ F) (hfg : f ≫ g = 0)
    (hS : ∀ T, (ShortComplex.mk (f.app T) (g.app T)
      (congrArg (fun h : D ⟶ F ↦ h.app T) hfg)).ShortExact) :
    ((ShortComplex.mk f g hfg).map orderedCechComplexFunctor).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  let S := ((ShortComplex.mk f g hfg).map orderedCechComplexFunctor).map
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) q)
  change S.ShortExact
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
    intro y
    constructor
    · intro h
      have hp (t : {t : Fin (q + 1) → ι // StrictMono t}) :
          ∃ x, (f.app (cechTupleSupport t.val)).hom x = y t :=
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS _).exact (y t)).mp
          (congrFun h t)
      exact ⟨fun t ↦ (hp t).choose, funext fun t ↦ (hp t).choose_spec⟩
    · rintro ⟨x, rfl⟩
      exact S.moduleCat_zero_apply x
  · apply (ModuleCat.mono_iff_injective S.f).mpr
    intro x y h
    funext t
    exact (ModuleCat.mono_iff_injective (f.app (cechTupleSupport t.val))).mp
      (hS _).mono_f (congrFun h t)
  · apply (ModuleCat.epi_iff_surjective S.g).mpr
    intro y
    have h (t : {t : Fin (q + 1) → ι // StrictMono t}) :=
      (ModuleCat.epi_iff_surjective (g.app (cechTupleSupport t.val))).mp (hS _).epi_g (y t)
    exact ⟨fun t ↦ (h t).choose, funext fun t ↦ (h t).choose_spec⟩

end Ordered

end SerrePositivity.AlgebraicGeometry

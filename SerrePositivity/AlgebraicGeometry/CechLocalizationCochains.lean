module

public import SerrePositivity.AlgebraicGeometry.CechLocalizationPi
public import Mathlib.Algebra.Exact.Basic
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizedColimit
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：有限被覆の全タプル Čech の各項と複体を、分数の局所化と比較する。
方針：有限積との比較を各次数に適用し、分母を固定した線形写像で交代和を移す。
規約：無限積との交換は使わない。係数図式の射との自然性を含む。
使われ方：標準被覆の増大完全性を局所化で調べ、単位イデアルから大域へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
open scoped BigOperators
universe u
variable {R : Type u} [CommRing R] (S : Submonoid R)
variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- 分数の局所化関手は加法的。 -/
instance cechLocalizationFunctorAdditive : (projectiveLocalizedModuleFunctor S).Additive where
  map_add {X Y f g} := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using LocalizedModule.induction_on with
    | _ m s =>
      simp only [projectiveLocalizedModuleFunctor, ModuleCat.hom_ofHom, ModuleCat.hom_add,
        LinearMap.add_apply, IsLocalizedModule.map_LocalizedModules,
        projectiveLocalizedModule_mk_add]

variable (D : Finset ι ⥤ ModuleCat.{u} R)

/-- 各 Čech 次数の局所化と、局所化した係数の Čech の項の比較。 -/
def cechLocalizationCochainsEquiv (k : ℕ) :
    LocalizedModule S (FullCechCochains D k) ≃ₗ[R]
      FullCechCochains (D ⋙ projectiveLocalizedModuleFunctor S) k :=
  cechLocalizationPiEquiv S (fun t : Fin k → ι ↦ (D.obj (cechTupleSupport t) : Type u))

/-- Čech の各項の局所化比較は、各タプルの分母を保つ。 -/
theorem cechLocalizationCochainsEquiv_mk (k : ℕ) (a : FullCechCochains D k) (s : S)
    (t : Fin k → ι) :
    cechLocalizationCochainsEquiv S D k (LocalizedModule.mk a s) t = LocalizedModule.mk (a t) s :=
  cechLocalizationPiEquiv_mk S _ a s t

/-- 各項の局所化比較は、増大項を含めて Čech の余境界と可換。 -/
theorem cechLocalizationCochainsEquiv_differential (k : ℕ) :
    (projectiveLocalizedModuleFunctor S).map (ModuleCat.ofHom (fullCechDifferential D k)) ≫
        (cechLocalizationCochainsEquiv S D (k + 1)).toModuleIso.hom =
      (cechLocalizationCochainsEquiv S D k).toModuleIso.hom ≫
        ModuleCat.ofHom (fullCechDifferential (D ⋙ projectiveLocalizedModuleFunctor S) k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using LocalizedModule.induction_on with
  | _ a s =>
    funext t
    change cechLocalizationCochainsEquiv S D (k + 1)
      (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
        (LocalizedModule.mkLinearMap S _) (fullCechDifferential D k) (LocalizedModule.mk a s)) t =
      fullCechDifferential (D ⋙ projectiveLocalizedModuleFunctor S) k
        (cechLocalizationCochainsEquiv S D k (LocalizedModule.mk a s)) t
    rw [IsLocalizedModule.map_LocalizedModules, cechLocalizationCochainsEquiv_mk,
      fullCechDifferential_apply, fullCechDifferential_apply]
    change LocalizedModule.mk
        (∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val •
          (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom (a (t ∘ i.succAbove))) s =
      ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val •
        (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
          (LocalizedModule.mkLinearMap S _) (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom)
          (cechLocalizationCochainsEquiv S D k (LocalizedModule.mk a s) (t ∘ i.succAbove))
    simp_rw [cechLocalizationCochainsEquiv_mk, IsLocalizedModule.map_LocalizedModules]
    let q : D.obj (cechTupleSupport t) →ₗ[R]
        LocalizedModule S (D.obj (cechTupleSupport t)) :=
      (LocalizedModule.divBy s).comp (LocalizedModule.mkLinearMap S _)
    have hq (x : D.obj (cechTupleSupport t)) : q x = LocalizedModule.mk x s := by
      simp [q, LocalizedModule.divBy_apply, LocalizedModule.liftOn_mk]
    have hsum := map_sum q (fun i : Fin (k + 1) ↦ (-1 : ℤ) ^ i.val •
      (D.map (homOfLE (cechTupleSupport_face_subset t i))).hom (a (t ∘ i.succAbove))) Finset.univ
    simp only [map_zsmul] at hsum
    simpa only [hq] using hsum

/-- 有限被覆の全タプル Čech 複体と、実際の分数の局所化との同型。 -/
def cechLocalizationComplexIso :
    ((projectiveLocalizedModuleFunctor S).mapHomologicalComplex (.up ℕ)).obj (fullCechComplex D) ≅
      fullCechComplex (D ⋙ projectiveLocalizedModuleFunctor S) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (cechLocalizationCochainsEquiv S D (q + 1)).toModuleIso) (by
      intro i j hij
      have h : i + 1 = j := hij
      subst j
      simpa only [Functor.mapHomologicalComplex_obj_d, fullCechComplex, CochainComplex.of_d]
        using (cechLocalizationCochainsEquiv_differential S D (i + 1)).symm)

/-- 各項の分数の比較は、係数図式の射に自然。 -/
theorem cechLocalizationCochainsEquiv_naturality
    {D E : Finset ι ⥤ ModuleCat.{u} R} (η : D ⟶ E) (k : ℕ) :
    (projectiveLocalizedModuleFunctor S).map (ModuleCat.ofHom (fullCechCochainsMap η k)) ≫
        (cechLocalizationCochainsEquiv S E k).toModuleIso.hom =
      (cechLocalizationCochainsEquiv S D k).toModuleIso.hom ≫ ModuleCat.ofHom
        (fullCechCochainsMap (Functor.whiskerRight η (projectiveLocalizedModuleFunctor S)) k) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using LocalizedModule.induction_on with
  | _ a s =>
    funext t
    change cechLocalizationCochainsEquiv S E k
      (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
        (LocalizedModule.mkLinearMap S _) (fullCechCochainsMap η k) (LocalizedModule.mk a s)) t =
      IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
        (LocalizedModule.mkLinearMap S _) (η.app (cechTupleSupport t)).hom
          (cechLocalizationCochainsEquiv S D k (LocalizedModule.mk a s) t)
    rw [IsLocalizedModule.map_LocalizedModules, cechLocalizationCochainsEquiv_mk,
      cechLocalizationCochainsEquiv_mk, IsLocalizedModule.map_LocalizedModules]
    rfl

/-- 元の Čech の余境界を、分数の局所化の間の写像にする。 -/
def cechLocalizedCochainsDifferential (k : ℕ) :
    LocalizedModule S (FullCechCochains D k) →ₗ[R]
      LocalizedModule S (FullCechCochains D (k + 1)) :=
  IsLocalizedModule.map S (LocalizedModule.mkLinearMap S _)
    (LocalizedModule.mkLinearMap S _) (fullCechDifferential D k)

/-- 局所化した余境界の比較の、元ごとの式。 -/
theorem cechLocalizationCochainsEquiv_differential_apply (k : ℕ)
    (z : LocalizedModule S (FullCechCochains D k)) :
    cechLocalizationCochainsEquiv S D (k + 1) (cechLocalizedCochainsDifferential S D k z) =
      fullCechDifferential (D ⋙ projectiveLocalizedModuleFunctor S) k
        (cechLocalizationCochainsEquiv S D k z) := by
  have h := congrArg (fun f ↦ f.hom z) (cechLocalizationCochainsEquiv_differential S D k)
  change cechLocalizationCochainsEquiv S D (k + 1) (cechLocalizedCochainsDifferential S D k z) =
    fullCechDifferential (D ⋙ projectiveLocalizedModuleFunctor S) k
      (cechLocalizationCochainsEquiv S D k z) at h
  exact h

/-- 局所化後の係数図式での完全性は、局所化した二つの余境界の完全性を与える。 -/
theorem cechLocalizationCochains_exact_of_exact (k : ℕ)
    (h : Function.Exact (fullCechDifferential (D ⋙ projectiveLocalizedModuleFunctor S) k)
      (fullCechDifferential (D ⋙ projectiveLocalizedModuleFunctor S) (k + 1))) :
    Function.Exact (cechLocalizedCochainsDifferential S D k)
      (cechLocalizedCochainsDifferential S D (k + 1)) := by
  let e0 := cechLocalizationCochainsEquiv S D k
  let e1 := cechLocalizationCochainsEquiv S D (k + 1)
  let e2 := cechLocalizationCochainsEquiv S D (k + 2)
  have h0 : (fullCechDifferential (D ⋙ projectiveLocalizedModuleFunctor S) k).comp
      e0.toLinearMap = e1.toLinearMap.comp (cechLocalizedCochainsDifferential S D k) := by
    apply LinearMap.ext
    intro z
    exact (cechLocalizationCochainsEquiv_differential_apply S D k z).symm
  have h1 : (fullCechDifferential (D ⋙ projectiveLocalizedModuleFunctor S) (k + 1)).comp
      e1.toLinearMap = e2.toLinearMap.comp (cechLocalizedCochainsDifferential S D (k + 1)) := by
    apply LinearMap.ext
    intro z
    exact (cechLocalizationCochainsEquiv_differential_apply S D (k + 1) z).symm
  exact (Function.Exact.iff_of_ladder_linearEquiv (e₁ := e0) (e₂ := e1) (e₃ := e2) h0 h1).mp h

end SerrePositivity.AlgebraicGeometry

module

public import SerrePositivity.AlgebraicGeometry.AffineModuleLocalizedCech
public import SerrePositivity.AlgebraicGeometry.OpenCoverCech
public import SerrePositivity.AlgebraicGeometry.CechCoefficientExactness
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
概要：Spec 上の局所化を与える前層について、標準開の Čech 完全性を得る。
方針：各標準開の切断を大域切断の局所化と自然に同定する。
規約：導来関手の層コホモロジーとの比較は使わない Čech 版。
使われ方：準連接層のアフィン被覆と共通アフィン細分への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite
universe u
variable {R : Type u} [CommRing R]
variable {M N : Type u} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/-- 局所化先では、分母を割る元の冪も可逆に作用する。 -/
theorem cechAwayFactorUnits {g a : R} (h : a ∣ g) (l : M →ₗ[R] N)
    [IsLocalizedModule (.powers g) l] (s : Submonoid.powers a) :
    IsUnit (algebraMap R (Module.End R N) s.val) := by
  obtain ⟨b, hb⟩ := h
  obtain ⟨_, n, rfl⟩ := s
  have hg : IsUnit (algebraMap R (Module.End R N) g) := by
    simpa using IsLocalizedModule.map_units l (⟨g, 1, pow_one g⟩ : Submonoid.powers g)
  have hab : IsUnit (algebraMap R (Module.End R N) a *
      algebraMap R (Module.End R N) b) := by
    rw [← map_mul, ← hb]
    exact hg
  have hc := (Commute.all a b).map (algebraMap R (Module.End R N))
  change IsUnit (algebraMap R (Module.End R N) (a ^ n))
  rw [map_pow]
  exact ((hc.isUnit_mul_iff.mp hab).1).pow n

variable (P : (Opens (PrimeSpectrum R))ᵒᵖ ⥤ ModuleCat.{u} R)
/-- Spec の大域切断から標準開への制限。 -/
def cechSpecRestriction (a : R) :
    P.obj (op (⊤ : Opens (PrimeSpectrum R))) →ₗ[R]
      P.obj (op (PrimeSpectrum.basicOpen a)) :=
  (P.map (homOfLE (show PrimeSpectrum.basicOpen a ≤ (⊤ : Opens (PrimeSpectrum R))
    from le_top)).op).hom

variable (hP : ∀ a : R, IsLocalizedModule (.powers a) (cechSpecRestriction P a))
variable {ι : Type} [LinearOrder ι] (f : ι → R)

/-- 分母の整除に沿う標準開の包含。 -/
theorem cechBasicOpen_le_of_dvd {a b : R} (h : a ∣ b) :
    PrimeSpectrum.basicOpen b ≤ PrimeSpectrum.basicOpen a := by
  obtain ⟨c, rfl⟩ := h
  rw [PrimeSpectrum.basicOpen_mul]
  exact inf_le_left

/-- 標準開の交叉上の切断を、積の標準開で表示する係数図式。 -/
def specStandardCechDiagram : Finset ι ⥤ ModuleCat.{u} R where
  obj T := P.obj (op (PrimeSpectrum.basicOpen (affineCechDenominator f T)))
  map {T S} h := P.map (homOfLE (cechBasicOpen_le_of_dvd
    (affineCechDenominator_dvd f (leOfHom h)))).op
  map_id T := by
    convert P.map_id _ using 1
  map_comp a b := by
    rw [← P.map_comp]
    congr 1

/-- 標準開の切断と大域切断の局所化の同型。 -/
def specStandardCechSectionIso (T : Finset ι) :
    (affineModuleCechDiagram (P.obj (op ⊤)) f).obj T ≅ (specStandardCechDiagram P f).obj T := by
  letI := hP (affineCechDenominator f T)
  exact (IsLocalizedModule.iso (.powers (affineCechDenominator f T))
    (cechSpecRestriction P (affineCechDenominator f T))).toModuleIso

/-- 標準開の切断と局所化の比較は、交叉を狭める制限に自然。 -/
theorem specStandardCechSectionIso_naturality {T S : Finset ι} (h : T ⊆ S) :
    (affineModuleCechDiagram (P.obj (op ⊤)) f).map (homOfLE h) ≫
        (specStandardCechSectionIso P hP f S).hom =
      (specStandardCechSectionIso P hP f T).hom ≫
        (specStandardCechDiagram P f).map (homOfLE h) := by
  let a := affineCechDenominator f T
  let b := affineCechDenominator f S
  let l := (cechSpecRestriction P b)
  letI := hP b
  letI := hP a
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext (.powers a) (LocalizedModule.mkLinearMap (.powers a) _)
    (cechAwayFactorUnits (affineCechDenominator_dvd f h) l)
  apply LinearMap.ext
  intro x
  change (IsLocalizedModule.iso (.powers b) l)
      (projectiveModuleAwayRestriction (affineCechDenominator_dvd f h)
        (LocalizedModule.mk x 1)) =
    ((specStandardCechDiagram P f).map (homOfLE h)).hom
      ((specStandardCechSectionIso P hP f T).hom.hom (LocalizedModule.mk x 1))
  rw [projectiveModuleAwayRestriction_mk_one, IsLocalizedModule.iso_mk_one]
  change l x = (P.map _).hom
    ((IsLocalizedModule.iso (.powers a)
      (cechSpecRestriction P a)) (LocalizedModule.mk x 1))
  letI := hP a
  rw [IsLocalizedModule.iso_mk_one]
  change (P.map _).hom x = (P.map _ ≫ P.map _).hom x
  rw [← P.map_comp]
  congr 2

/-- 局所化を与える前層の、標準開係数図式との自然同型。 -/
def specStandardCechDiagramIso :
    affineModuleCechDiagram (P.obj (op ⊤)) f ≅ specStandardCechDiagram P f :=
  NatIso.ofComponents (specStandardCechSectionIso P hP f)
    (fun h ↦ specStandardCechSectionIso_naturality P hP f (leOfHom h))

include hP in
/-- 局所化を与える前層の標準開被覆では、増大項からの写像は単射。 -/
theorem specStandardCech_zero_injective [Fintype ι]
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (fullCechDifferential (specStandardCechDiagram P f) 0) :=
  fullCechCoefficientEquiv_zero_injective (specStandardCechDiagramIso P hP f)
    (affineModuleCech_zero_injective (P.obj (op ⊤)) f hspan)

include hP in
/-- 局所化を与える前層の標準開被覆の増大 Čech 完全性。
原典 Stacks 30.2.1 の Hⁱ の消滅の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem specStandardCech_exact [Fintype ι]
    (hspan : Ideal.span (Set.range f) = ⊤) (k : ℕ) :
    Function.Exact (fullCechDifferential (specStandardCechDiagram P f) k)
      (fullCechDifferential (specStandardCechDiagram P f) (k + 1)) :=
  fullCechCoefficientEquiv_exact (specStandardCechDiagramIso P hP f) k
    (affineModuleCech_exact (P.obj (op ⊤)) f hspan k)

/-- 分母の積の標準開は、各分母の標準開の有限交叉。 -/
theorem cechBasicOpen_denominator (T : Finset ι) :
    PrimeSpectrum.basicOpen (affineCechDenominator f T) =
      cechOpenIntersection (fun i ↦ PrimeSpectrum.basicOpen (f i)) T := by
  induction T using Finset.induction_on with
  | empty => simp [affineCechDenominator, cechOpenIntersection]
  | @insert i T hi ih =>
    simp only [affineCechDenominator, Finset.prod_insert hi, PrimeSpectrum.basicOpen_mul]
    rw [← affineCechDenominator, ih]
    change PrimeSpectrum.basicOpen (f i) ⊓
        cechOpenIntersection (fun j ↦ PrimeSpectrum.basicOpen (f j)) T =
      cechOpenIntersection (fun j ↦ PrimeSpectrum.basicOpen (f j)) (insert i T)
    apply le_antisymm
    · apply le_iInf
      intro j
      apply le_iInf
      intro hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact inf_le_left
      · exact inf_le_right.trans (iInf_le_of_le j (iInf_le_of_le hj le_rfl))
    · exact le_inf (iInf_le_of_le i
        (iInf_le_of_le (Finset.mem_insert_self i T) le_rfl))
        (cechOpenIntersection_antitone _ (Finset.subset_insert i T))

/-- 積の標準開による図式と、実際の有限交叉による図式の自然同型。 -/
def specStandardCechOpenDiagramIso : specStandardCechDiagram P f ≅
    openCoverCechDiagram P (fun i ↦ PrimeSpectrum.basicOpen (f i)) :=
  NatIso.ofComponents (fun T ↦ P.mapIso (eqToIso (congrArg op
    (cechBasicOpen_denominator f T)))) (by
      intro T S h
      change P.map _ ≫ P.map _ = P.map _ ≫ P.map _
      rw [← P.map_comp, ← P.map_comp]
      congr 1)

include hP in
/-- Spec の標準開被覆上の実際の切断の増大 Čech の完全性。
原典 Stacks 30.2.1 の Hⁱ の消滅の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem specStandardOpenCech_exact [Fintype ι]
    (hspan : Ideal.span (Set.range f) = ⊤) (k : ℕ) :
    Function.Exact
      (fullCechDifferential (openCoverCechDiagram P (fun i ↦ PrimeSpectrum.basicOpen (f i))) k)
      (fullCechDifferential (openCoverCechDiagram P (fun i ↦ PrimeSpectrum.basicOpen (f i)))
        (k + 1)) :=
  fullCechCoefficientEquiv_exact (specStandardCechOpenDiagramIso P f) k
    (specStandardCech_exact P hP f hspan k)

end SerrePositivity.AlgebraicGeometry

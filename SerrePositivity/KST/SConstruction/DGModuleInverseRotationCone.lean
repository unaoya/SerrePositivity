module
public import SerrePositivity.KST.SConstruction.DGModuleConnectingConeComparison
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
public import SerrePositivity.DifferentialGraded.Module.Graded

/-!
概要：元の実逆 shift connecting 射の cone を、元終域へ比較する。
方針：同じ実 cone／shift 同型、connecting cone 比較、指定 shift 相殺を合成する。
規約：同型な cone への選び直しは行わない。使われ方：実逆回転後の商合成比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：同じ実 shift 射は元 K(D) 同値を保つ。
方針：商関手の指定 shift 比較と元 shift 関手の同値保存を使う。
規約：同じ元 shift 射を保持。使われ方：逆回転比較の可逆性。 -/
lemma dgModuleShiftMap_isIso {M N : ModuleCategory R D} (f : M ⟶ N) (s : ℤ)
    (hf : IsIso ((moduleToHomotopy R D).map f)) :
    IsIso ((moduleToHomotopy R D).map (moduleShiftMap R D s f)) := by
  letI := hf
  exact (NatIso.isIso_map_iff ((moduleToHomotopy R D).commShiftIso s) f).2
    (inferInstanceAs (IsIso ((shiftFunctor (ModuleHomotopyCategory R D) s).map
      ((moduleToHomotopy R D).map f))))

/-- 概要：元 cone／shift 実同型は同じ元包含を厳密に保持する。
方針：元の同じ両辺の符号を二度の作用で消去する。
規約：元符号式から導く。使われ方：実逆回転比較の包含制限。 -/
lemma dgModuleConeShift_inr {M N : ModuleCategory R D} (f : M ⟶ N) (s : ℤ) :
    moduleShiftMap R D s (moduleConeInr R D f) ≫ (moduleConeShiftIso R D s f).hom =
      moduleConeInr R D (moduleShiftMap R D s f) := by
  change moduleShiftMap R D s (moduleConeInr R D f) ≫ moduleConeShiftHom R D s f = _
  have h := congrArg (fun k => s.negOnePow • k) (moduleConeShift_inr R D s f)
  simpa only [Linear.units_smul_comp, Linear.comp_units_smul, Category.id_comp,
    smul_smul, Int.units_mul_self, one_smul] using h

/-- 概要：元包含の後の同じ cone／shift 逆射は元包含の実 shift。
方針：元同型の順逆律と同じ包含回収を使う。
規約：同じ実逆射を保持。使われ方：逆回転 cone 比較の境界。 -/
lemma dgModuleConeShift_inr_inv {M N : ModuleCategory R D} (f : M ⟶ N) (s : ℤ) :
    moduleConeInr R D (moduleShiftMap R D s f) ≫ (moduleConeShiftIso R D s f).inv =
      moduleShiftMap R D s (moduleConeInr R D f) := by
  rw [← dgModuleConeShift_inr R D f s, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {M N : ModuleCategory R D} (f : M ⟶ N)

/-- 概要：元終域 shift 1 と逆 shift の指定相殺同型。
方針：元の shift 加法・零 shift の実同型を合成する。
規約：元二重 shift を保持。使われ方：実逆回転の終域回収。 -/
def dgModuleInverseRotationTargetIso :
    moduleShiftObj R D (-1) (moduleShiftObj R D 1 N) ≅ N :=
  (moduleShiftAddIsoObj R D 1 (-1) (ForgetEnrichment.to (Complex R) N)).symm ≪≫
    moduleShiftZeroIsoObj R D (ForgetEnrichment.to (Complex R) N)

/-- 概要：元実逆 shift connecting 射の同じ cone から元終域への実比較。
方針：同じ cone／shift 同型の逆と指定実 connecting cone 比較・相殺を合成する。
規約：元の射を変更しない。使われ方：LT 実中央射・実差の合成の元比較。 -/
def dgModuleInverseRotationConeComparison :
    moduleCone R D (moduleShiftMap R D (-1) (moduleConeConnecting R D f)) ⟶ N :=
  (moduleConeShiftIso R D (-1) (moduleConeConnecting R D f)).inv ≫
    moduleShiftMap R D (-1) (dgModuleConnectingConeComparison R D f) ≫
      (dgModuleInverseRotationTargetIso R D (N := N)).hom

/-- 概要：指定された同じ実逆回転 cone 比較は K(D) で同値。
方針：元二つの実同型と同じ connecting cone 比較の shift 同値を合成する。
規約：対象別存在選択で比較射を置き換えない。使われ方：native 全比較の成分判定。 -/
lemma dgModuleInverseRotationConeComparison_isIso :
    IsIso ((moduleToHomotopy R D).map (dgModuleInverseRotationConeComparison R D f)) := by
  haveI := dgModuleShiftMap_isIso R D (dgModuleConnectingConeComparison R D f) (-1)
    (dgModuleConnectingConeComparison_isIso R D f)
  rw [dgModuleInverseRotationConeComparison, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  infer_instance

private lemma shiftCompositePostcomp_eq (s : ℤ) {A₀ B₀ C₀ L₀ : ModuleCategory R D}
    (a : A₀ ⟶ B₀) (b : B₀ ⟶ C₀) (k : moduleShiftObj R D s C₀ ⟶ L₀) :
    (moduleShiftMap R D s a ≫ moduleShiftMap R D s b) ≫ k =
      moduleShiftMap R D s (a ≫ b) ≫ k :=
  congrArg (fun z => z ≫ k) ((moduleShiftFunctor R D s).map_comp a b).symm

/-- 概要：同じ実逆回転 cone 比較の包含制限は前段の包含制限の実逆 shift。
方針：元 cone／shift 逆射の包含式と元 shift の合成保存を使用する。
規約：前段で計算した負符号と同じ指定相殺を保持。使われ方：実商合成の指定三角形。 -/
lemma dgModuleInverseRotationConeComparison_inr :
    moduleConeInr R D (moduleShiftMap R D (-1) (moduleConeConnecting R D f)) ≫
      dgModuleInverseRotationConeComparison R D f =
      moduleShiftMap R D (-1) (moduleConeInr R D (moduleConeConnecting R D f) ≫
        dgModuleConnectingConeComparison R D f) ≫
        (dgModuleInverseRotationTargetIso R D (N := N)).hom := by
  rw [dgModuleInverseRotationConeComparison, ← Category.assoc,
    dgModuleConeShift_inr_inv, ← Category.assoc]
  exact shiftCompositePostcomp_eq R D (-1)
    (moduleConeInr R D (moduleConeConnecting R D f))
    (dgModuleConnectingConeComparison R D f) (dgModuleInverseRotationTargetIso R D (N := N)).hom

end SerrePositivity.KST.SConstruction

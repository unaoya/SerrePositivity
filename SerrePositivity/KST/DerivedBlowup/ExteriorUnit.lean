module

public import SerrePositivity.KST.DerivedBlowup.ExteriorMultiplication
public import SerrePositivity.DifferentialGraded.Complexes.Unit

/-!
概要：KST Def3.1 の整数次数 Koszul 外積複体に単位射を構成する。
方針：第0外積の1を複体へ戻し、閉次数0の元からの既存構成を用いる。
規約：既存 dg 複体の tensor unit を使う。
使われ方：一対象 dg 圏としての Koszul チャートの単位。
-/

@[expose] public noncomputable section

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：第0外積の1に対応する次数0の元。
方針：非正次数の標準同型の逆写像を使う。
規約：KST Def3.1。使われ方：Koszul 複体の単位 cycle。 -/
def exteriorUnitElement (d : M →ₗ[R] R) : (exteriorKoszulCochain d).X 0 :=
  (exteriorCochainXIsoNonpos d 0 (by omega)).inv.hom (exteriorDegreeUnit (M := M) 1)

/-- 概要：単位元の総外積への像は1。
方針：標準同型の往復と algebraMap の1保存を用いる。
規約：KST Def3.1。使われ方：左右の単位則を総外積で比較する。 -/
@[simp] theorem exteriorUnitElement_inclusion (d : M →ₗ[R] R) :
    exteriorCochainInclusion d 0 (exteriorUnitElement d) = 1 := by
  rw [exteriorUnitElement, exteriorCochainInclusion_inv]
  exact map_one (algebraMap R (ExteriorAlgebra R M))

/-- 概要：単位元は閉次数0の cycle。
方針：正次数の項の零対象性を使う。
規約：KST Def3.1。使われ方：単位複体からの chain map を構成する。 -/
def exteriorUnitCycle (d : M →ₗ[R] R) : DifferentialGraded.zeroCycles (exteriorKoszulCochain d) :=
  ⟨exteriorUnitElement d, by
    have := ModuleCat.subsingleton_of_isZero (exteriorKoszulCochain_isZero_X_pos d 1 (by omega))
    exact Subsingleton.elim _ _⟩

/-- 概要：Koszul 外積複体の tensor unit からの単位 chain map。
方針：構成済みの単位 cycle を unitFromCycle に渡す。
規約：KST Def3.1。使われ方：Koszul dg 代数の一対象豊穣構造。 -/
def exteriorKoszulUnit (d : M →ₗ[R] R) :
    𝟙_ (DifferentialGraded.Complex R) ⟶ exteriorKoszulCochain d :=
  DifferentialGraded.unitFromCycle _ (exteriorUnitCycle d)

/-- 概要：単位射の次数0成分は基底環の係数を総外積へ送る。
方針：単位 cycle の構成と包含の線形性を使う。
規約：KST Def3.1。使われ方：tensor unit の左右の単位則。 -/
theorem exteriorKoszulUnit_inclusion (d : M →ₗ[R] R) (r : R) :
    exteriorCochainInclusion d 0 ((exteriorKoszulUnit d).f 0 r) =
      algebraMap R (ExteriorAlgebra R M) r := by
  dsimp only [exteriorKoszulUnit, DifferentialGraded.unitFromCycle]
  rw [HomologicalComplex.mkHomFromSingle_f]
  change exteriorCochainInclusion d 0 (r • exteriorUnitElement d) = _
  rw [map_smul, exteriorUnitElement_inclusion, Algebra.smul_def, mul_one]

end SerrePositivity.KST.DerivedBlowup

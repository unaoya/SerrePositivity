module
public import SerrePositivity.KST.SConstruction.DGKappaNativeCoherentBFBoundary
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFArrowNaturality

/-!
概要：実 Φ の新四辺と旧 kSpectrumMap の全整数群作用を接続する。
方針：元の四完全射を回収し、同じ指定群同型の自然性を四辺へ制限する。
規約：旧公開型は不変。使われ方：K-B・K-cof の旧整数群と新有限 BF 四角形の接続。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra LocalizingInvariants Fibration
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

local instance nativeCoherentBFArrowComparisonTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 概要：有限入力の同じ四射は元の四完全射を端点ごと回収する。
方針：元の四対象と四射の定義を照合する。
規約：Arrow の等号。使われ方：旧 kSpectrumMap の元射との同定。 -/
lemma dgKappaNativeBFFiniteNativeArrow_forget (e : Fin 4) :
    Arrow.mk (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).hom.hom =
      dgKappaNativeBFNativeArrow.{u, v} R D I e := by
  fin_cases e <;> rfl

/-- 概要：新しい四辺の始域と旧値の全整数群の指定同型。
方針：同じ実正段比較を元始域の標準正段で使う。
規約：全整数次数。使われ方：旧 π 作用との可換性の始域。 -/
def dgKappaNativeCoherentBFArrowSourceIntegerEquiv (e : Fin 4) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum (sInputModel
      (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).left.obj)) j ≃*
        OmegaSpectrum.homotopyGroup (dgKappaNativeCoherentBFArrow.{u, v} R D I e).left j :=
  dgKappaNativeBFIntegerComparisonEquiv.{u, v} R D I
    (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).left j

/-- 概要：新しい四辺の終域と旧値の全整数群の指定同型。
方針：同じ実正段比較を元終域の標準正段で使う。
規約：全整数次数。使われ方：旧 π 作用との可換性の終域。 -/
def dgKappaNativeCoherentBFArrowTargetIntegerEquiv (e : Fin 4) (j : ℤ) :
    OmegaSpectrum.homotopyGroup (kOmegaSpectrum (sInputModel
      (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).right.obj)) j ≃*
        OmegaSpectrum.homotopyGroup (dgKappaNativeCoherentBFArrow.{u, v} R D I e).right j :=
  dgKappaNativeBFIntegerComparisonEquiv.{u, v} R D I
    (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).right j

/-- 概要：実 Φ の新四辺と元の旧 kSpectrumMap は指定同型で全整数 π 作用が可換。
方針：同じ元四射について全正段の成分自然性を標準段で評価する。
規約：辺の厳密等式を要求せず、全次数の指定群同型との可換性を保持する。
使われ方：K-B の有限四角形と K-cof の元の整数群作用を接続する。 -/
lemma dgKappaNativeCoherentBFArrow_homotopyMap_eq (e : Fin 4) (j : ℤ) :
    (OmegaSpectrum.homotopyMap (dgKappaNativeCoherentBFArrow.{u, v} R D I e).hom j).comp
      (dgKappaNativeCoherentBFArrowSourceIntegerEquiv.{u, v} R D I e j).toMonoidHom =
        (dgKappaNativeCoherentBFArrowTargetIntegerEquiv.{u, v} R D I e j).toMonoidHom.comp
          (OmegaSpectrum.homotopyMap (kSpectrumMap (sInputExactMap
            (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).hom.hom)) j) :=
  dgKappaNativeBFIntegerComparison_naturality.{u, v} R D I
    (dgKappaNativeBFFiniteNativeArrow.{u, v} R D I e).hom j

end SerrePositivity.KST.SConstruction

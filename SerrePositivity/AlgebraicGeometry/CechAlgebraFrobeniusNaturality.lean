module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusH0
public import SerrePositivity.AlgebraicGeometry.CechAlgebraEqualizerMap
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitIntNaturality

/-!
概要：係数代数の射に対する Frobenius 系と Čech H⁰ 比較の自然性。
方針：各交叉の実際の環準同型を整数線形に忘却し、Frobenius との可換性を使う。
規約：適合切断への射は既存の成分ごとの代数写像。
使われ方：F7 の閉厚化の四角形を同じ Čech H⁰ の射に移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]
variable {D E : Finset ι ⥤ CommAlgCat.{u} R} (η : D ⟶ E)

/-- 代数係数の射を、スカラー制限した整数加群の射として読む。 -/
def algebraCechIntMap : algebraCechIntDiagram D ⟶ algebraCechIntDiagram E :=
  whiskerRight (whiskerRight η
    (forget₂ (CommAlgCat R) (AlgCat R) ⋙ forget₂ (AlgCat R) (ModuleCat R)))
      (ModuleCat.restrictScalars (Int.castRingHom R))

/-- 整数線形として適合切断へ送っても、既存の代数写像と同じ関数。 -/
theorem fullAlgebraCechEqualizerAddMap_intMap (a : fullAlgebraCechEqualizer D) :
    fullAlgebraCechEqualizerAddMap (algebraCechIntMap η) a =
      fullAlgebraCechEqualizerMap η a := rfl

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

/-- 代数係数の射は、実際の Frobenius 係数系の自然変換を誘導する。 -/
def algebraCechFrobeniusCoefficientNatTrans :
    algebraCechFrobeniusCoefficientFunctor D p hp hR ⟶
      algebraCechFrobeniusCoefficientFunctor E p hp hR where
  app _ := algebraCechIntMap η
  naturality {i j} f := by
    apply NatTrans.ext
    funext T
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact frobeniusDirectSystemMap_naturality p hp
      (algebraCech_primeCast D p hR T) (algebraCech_primeCast E p hR T)
      (η.app T).hom.toRingHom i j (leOfHom f) x

/-- 各段の H⁰ の同型は、実際の適合切断の写像と係数系の写像を比較する。 -/
theorem algebraCechFrobeniusH0SystemIso_naturality :
    frobeniusIntDirectSystemNatTrans p hp
      (algebraCechEqualizer_primeCast D p hR) (algebraCechEqualizer_primeCast E p hR)
      (fullAlgebraCechEqualizerMap η).toRingHom ≫
        (algebraCechFrobeniusH0SystemIso E p hp hR).hom =
    (algebraCechFrobeniusH0SystemIso D p hp hR).hom ≫
      whiskerRight (algebraCechFrobeniusCoefficientNatTrans η p hp hR)
        (fullCechComplexFunctor ⋙
          HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0) := by
  apply NatTrans.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have h := fullAlgebraCechIntH0Equiv_naturality (algebraCechIntMap η) a
  rw [fullAlgebraCechEqualizerAddMap_intMap] at h
  exact h

end SerrePositivity.AlgebraicGeometry

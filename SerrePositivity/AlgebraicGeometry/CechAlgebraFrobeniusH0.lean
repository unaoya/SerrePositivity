module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraFrobeniusSystem
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechIntSequential

/-!
概要：Frobenius 係数順極限の Čech H⁰ と、適合切断環の Frobenius 順極限を比較する。
方針：各段の H⁰ の自然性を有向系の同型にし、既存の filtered 余極限比較を使う。
規約：順極限を取る前後で実際の係数写像を保つ。
使われ方：F7 の切断環の短完全列を Čech H⁰ の四角形に移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]
variable (D : Finset ι ⥤ CommAlgCat.{u} R) (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0)

/-- 適合切断環の Frobenius 系と、各段の整数係数 Čech H⁰ の系の自然同型。 -/
def algebraCechFrobeniusH0SystemIso :
    linearDirectSystemFunctor (ringDirectSystemIntMap
      (frobeniusDirectSystemMap (fullAlgebraCechEqualizer D) p hp
        (algebraCechEqualizer_primeCast D p hR))) ≅
      algebraCechFrobeniusCoefficientFunctor D p hp hR ⋙ fullCechComplexFunctor ⋙
        HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) 0 :=
  NatIso.ofComponents (fun _ ↦ (fullAlgebraCechIntH0Equiv D).toModuleIso) (by
    intro i j f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    have h := fullAlgebraCechIntH0Equiv_naturality
      (algebraCechIntFrobeniusSystemMap D p hp hR i j (leOfHom f)) a
    rw [fullAlgebraCechEqualizerAddMap_frobenius] at h
    exact h)

variable [Fintype ι]

/-- Frobenius 係数順極限の Čech H⁰ は、適合切断環の Frobenius 順極限と同型。
BST13 Lemma 3.8・3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def algebraCechFrobeniusH0ColimitIso :
    (fullCechComplex (colimit (algebraCechFrobeniusCoefficientFunctor D p hp hR))).homology 0 ≅
      ModuleCat.of ℤ (FrobeniusDirectLimit (fullAlgebraCechEqualizer D) p hp
        (algebraCechEqualizer_primeCast D p hR)) :=
  projectiveIntCechSequentialHomologyIso (algebraCechFrobeniusCoefficientFunctor D p hp hR) 0 ≪≫
    colim.mapIso (algebraCechFrobeniusH0SystemIso D p hp hR).symm ≪≫
      (ringDirectLimitIntColimitIso
        (frobeniusDirectSystemMap (fullAlgebraCechEqualizer D) p hp
          (algebraCechEqualizer_primeCast D p hR))).symm

end SerrePositivity.AlgebraicGeometry

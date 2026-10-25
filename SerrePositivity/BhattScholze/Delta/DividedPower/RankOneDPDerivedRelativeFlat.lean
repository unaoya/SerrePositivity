module

public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPDerivedKoszul
public import SerrePositivity.BhattScholze.Delta.DividedPower.RankOneDPTruncatedTensorFlat

/-! # 分冪導来拡大の実ホモロジーの相対平坦性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} {A : Type u} [CommRing A]
variable (hprime : p.Prime) (hp : (p : A) = 0)
local notation "P₀" => Polynomial A
local notation "C₀" => AdjoinRoot ((Polynomial.X : P₀) ^ p)
local notation "G₀" => DividedPowerAlgebra A A
local notation "q₀" => AdjoinRoot.mk ((Polynomial.X : P₀) ^ p)

/-- 実係数拡大を元の係数環へ制限した加群は、元の制限加群の可算直和と同値。 -/
def rankOneDPTruncatedExtensionEquiv (M : ModuleCat.{u} C₀) :
    ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((ModuleCat.extendScalars (rankOneDPTruncatedMap hprime.pos hp).toRingHom).obj M)) ≃ₗ[A]
      (ℕ →₀ ((ModuleCat.restrictScalars (algebraMap A C₀)).obj M)) := by
  let : Algebra C₀ G₀ := rankOneDPTruncatedAlgebra hprime.pos hp
  let : Module A M := Module.compHom M (algebraMap A C₀)
  let : IsScalarTower A C₀ M := IsScalarTower.of_compHom A C₀ M
  let e := rankOneDPTruncatedTensorEquiv hprime hp M
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a z
  have hact : ∀ z : G₀ ⊗[C₀] M, (algebraMap A G₀ a) • z = a • z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul g m =>
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
        congr 1
        exact (Algebra.smul_def a g).symm
    | add z w hz hw => simp only [smul_add, hz, hw]
  change e ((algebraMap A G₀ a) • z) = a • e z
  rw [hact, e.map_smul]

/-- 実係数拡大は、係数制限で明示したA平坦性を保存・反映する。 -/
theorem rankOneDPTruncatedExtension_flat_iff (M : ModuleCat.{u} C₀) :
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((ModuleCat.extendScalars (rankOneDPTruncatedMap hprime.pos hp).toRingHom).obj M)) ↔
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A C₀)).obj M) := by
  have hf : Module.Flat A (ℕ →₀ ((ModuleCat.restrictScalars (algebraMap A C₀)).obj M)) ↔
      Module.Flat A ((ModuleCat.restrictScalars (algebraMap A C₀)).obj M) := by
    rw [Module.Flat.equiv_iff
      (finsuppLEquivDirectSum A ((ModuleCat.restrictScalars (algebraMap A C₀)).obj M) ℕ),
      Module.Flat.directSum_iff]
    simp only [forall_const]
  exact (Module.Flat.equiv_iff (rankOneDPTruncatedExtensionEquiv hprime hp M)).trans hf

include hprime hp in
/-- 分冪代数への実導来拡大の各ホモロジーのA平坦性は、切断多項式側と同値。 -/
theorem rankOneDPDerivedHomology_flat_iff
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj))) ↔
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A C₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj))) :=
  (Module.Flat.equiv_iff
    (((ModuleCat.restrictScalars (algebraMap A G₀)).mapIso
      (rankOneDPDerivedHomologyIso hprime hp X n)).toLinearEquiv)).trans
    (rankOneDPTruncatedExtension_flat_iff hprime hp _)

/-- 実Koszulホモロジーの比較は、元のA係数作用を保つ線形同値でもある。 -/
def rankOneDPTruncationKoszulRelativeHomologyEquiv
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    ((ModuleCat.restrictScalars (algebraMap A P₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
        ((DerivedCompletion.derivedScalarConeFunctor P₀
          ((Polynomial.X : P₀) ^ p)).obj X.obj))) ≃ₗ[A]
    ((ModuleCat.restrictScalars (algebraMap A C₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} C₀) n).obj
        (((boundedAboveDerivedBaseChange q₀).obj X).obj))) :=
  (((ModuleCat.restrictScalars (algebraMap A P₀)).mapIso
    (rankOneDPTruncationHomologyKoszulIso (p := p) X n)).toLinearEquiv)

include hprime hp in
/-- 実分冪導来拡大の各ホモロジーのA平坦性は、実X^p KoszulホモロジーのA平坦性と同値。 -/
theorem rankOneDPDerivedKoszulHomology_flat_iff
    (X : DerivedCategory.Minus (ModuleCat.{u} P₀)) (n : ℤ) :
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A G₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} G₀) n).obj
        (((boundedAboveDerivedBaseChange (rankOneDPPolynomialMap A).toRingHom).obj X).obj))) ↔
    Module.Flat A ((ModuleCat.restrictScalars (algebraMap A P₀)).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} P₀) n).obj
        ((DerivedCompletion.derivedScalarConeFunctor P₀ ((Polynomial.X : P₀) ^ p)).obj X.obj))) :=
  (rankOneDPDerivedHomology_flat_iff hprime hp X n).trans
    (Module.Flat.equiv_iff (rankOneDPTruncationKoszulRelativeHomologyEquiv X n)).symm

end SerrePositivity.BhattScholze

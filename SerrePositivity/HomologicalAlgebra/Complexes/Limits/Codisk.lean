module

public import SerrePositivity.HomotopicalAlgebra.Complexes.ProjectiveModel
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES

/-!
# 各次数の線形射を受け取る実可縮 disk

概要：Pⁿ→M を次数 n−1,n の可縮複体への実射へ送る。
方針：恒等 mapping cocone に、指定した −1-cochain とその境界を持ち上げる。
規約：任意の加群 M に対し、射影性や有限性を仮定しない。
使われ方：実射影 cofibrant 複体の各次数の射影性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.CochainComplex _root_.CochainComplex.HomComplex
open _root_.SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

def codisk (M : ModuleCat.{u} A) (n : ℤ) : Complex A :=
  mappingCocone (𝟙 ((single (ModuleCat A) (.up ℤ) (n - 1)).obj M))
def codiskHom {P : Complex A} {M : ModuleCat.{u} A} (n : ℤ)
    (a : P.X n ⟶ M) : P ⟶ _root_.SerrePositivity.ComplexLimits.codisk M n := by
  let K := (single (ModuleCat A) (.up ℤ) (n - 1)).obj M
  let β : Cochain P K (-1) := Cochain.single
    (a ≫ (singleObjXSelf (.up ℤ) (n - 1) M).inv) (-1)
  let α : Cocycle P K 0 := Cocycle.mk (-δ (-1) 0 β) 1 (by simp) (by simp [δ_neg, δ_δ])
  exact (mappingCocone.liftCocycle (𝟙 K) α β (by simp) (by simp [α])).homOf
lemma codiskHom_recovery {P : Complex A} {M : ModuleCat.{u} A} (n : ℤ) (a : P.X n ⟶ M) :
    (_root_.SerrePositivity.ComplexLimits.codiskHom n a).f n ≫
      (mappingCocone.snd (𝟙 ((single (ModuleCat A) (.up ℤ) (n - 1)).obj M))).v
        n (n - 1) (by omega) ≫ (singleObjXSelf (.up ℤ) (n - 1) M).hom = a := by
  simp only [_root_.SerrePositivity.ComplexLimits.codiskHom, Cocycle.homOf_f, mappingCocone.liftCocycle_coe,
    mappingCocone.liftCochain_v_snd_v_assoc, Cochain.single_v, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

lemma codisk_acyclic (M : ModuleCat.{u} A) (n : ℤ) : (_root_.SerrePositivity.ComplexLimits.codisk M n).Acyclic :=
  _root_.SerrePositivity.cochainAcyclic_shift ((complex_quasiIso_iff_acyclic_cone A
    (𝟙 ((single (ModuleCat A) (.up ℤ) (n - 1)).obj M))).mp inferInstance) (-1)

end SerrePositivity.ComplexLimits

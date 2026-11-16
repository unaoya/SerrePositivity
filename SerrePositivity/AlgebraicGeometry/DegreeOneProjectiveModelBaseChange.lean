module

public import SerrePositivity.AlgebraicGeometry.DegreeOneProjectiveModelCechData
public import SerrePositivity.AlgebraicGeometry.ProjectiveCoefficientPullback
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
概要：元の次数一表示を、任意の係数移送の同じpullbackの表示へ送る。
方針：既存のProjのCartesianな係数移送と、テンソルした次数一評価の全射性を使う。
規約：平坦性を仮定せず、blowup自体の任意の基底変更との可換性は主張しない。
使われ方：固定した固有射のNoether帰納の任意のアフィン基底変更。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 同じ全射な次数一評価の生成元を1⊗aへ送ると、任意の係数移送後も全射。 -/
theorem degreeOne_baseChange_aeval_surjective {R A B : Type u} {ι : Type}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (a : ι → A) (ha : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    Function.Surjective (MvPolynomial.aeval (R := B)
      (fun i ↦ (1 : B) ⊗ₜ[R] a i)) := by
  let M : B ⊗[R] MvPolynomial ι R →ₐ[B] B ⊗[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) (MvPolynomial.aeval a)
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := ι) R B
  have hM : Function.Surjective M :=
    Algebra.TensorProduct.map_surjective (AlgHom.id B B) (MvPolynomial.aeval a)
      Function.surjective_id ha
  have he : M.comp e.symm.toAlgHom = MvPolynomial.aeval (R := B)
      (fun i ↦ (1 : B) ⊗ₜ[R] a i) := by
    ext i
    simp [M, e]
  rw [← he]
  exact hM.comp e.symm.surjective

set_option backward.isDefEq.respectTransparency false in
/-- 同じ次数一表示は、任意の環の射の実際のSpecへのpullbackにも移る。 -/
def DegreeOneProjectiveModel.baseChange {R B : Type u} [CommRing R] [CommRing B]
    {Y : Scheme.{u}} {f : Y ⟶ Spec (CommRingCat.of R)}
    (m : DegreeOneProjectiveModel f) (ρ : R →+* B) :
    DegreeOneProjectiveModel (pullback.snd f (Spec.map (CommRingCat.ofHom ρ))) := by
  letI : Algebra R B := ρ.toAlgebra
  let G := fun n ↦ (m.grade n).baseChange B
  let a : m.index → B ⊗[R] m.ring := fun i ↦ (1 : B) ⊗ₜ[R] m.generator i
  have ha : ∀ i, a i ∈ G 1 := fun i ↦
    Submodule.tmul_mem_baseChange_of_mem (1 : B) (m.homogeneous i)
  have hs : Function.Surjective (MvPolynomial.aeval (R := B) a) :=
    degreeOne_baseChange_aeval_surjective m.generator m.surjective
  let n := degreeOneProjectiveModelOfProj G a ha hs
  have hspan := degreeOne_irrelevant_le_span m.grade m.generator m.homogeneous m.surjective
  have H := isPullback_projectiveCoefficientMap (B := B) m.grade m.generator m.homogeneous hspan
  have hm : m.iso.inv ≫ f = projectiveCechStructureMap m.grade :=
    (m.iso.inv_comp_eq).mpr m.over.symm
  have H' : IsPullback (projectiveCoefficientMap (B := B) m.grade ≫ m.iso.inv)
      (projectiveCechStructureMap G) f (Spec.map (CommRingCat.ofHom ρ)) := by
    refine H.of_iso (Iso.refl _) m.iso.symm (Iso.refl _) (Iso.refl _)
      (by simp [G] <;> rfl) (by simp [G] <;> rfl) ?_ (by simp [G] <;> rfl)
    simpa only [Iso.refl_hom, Category.comp_id, Iso.symm_hom] using hm.symm
  exact H'.isoPullback_inv_snd ▸ n.ofIso H'.isoPullback.symm

end SerrePositivity.AlgebraicGeometry

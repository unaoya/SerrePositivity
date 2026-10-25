module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHomCodeFunctorLift
/-!
概要：係数 span に入る斉次射を固定基底コードへ持ち上げ、実評価と閉性を厳密に保持する。
方針：コードから係数閉包への Hom 同型の逆で持ち上げ、単射な実評価で微分零を反映する。
規約：全次数と元の端点ラベルを保持する。
使われ方：c′ の追加係数から実閉射・cone の精密化を回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {I : Type u} (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]
  (κ : Cardinal.{u}) (a : κ.ord.ToType) (source target : I → Set.Iio a) (degree : I → ℤ)
  (value : Set.Iio a → D)
  (coefficient : ∀ i, GradedHom R (value (source i)) (value (target i)) (degree i))
  (hκ : Cardinal.aleph0 ≤ κ) (hI : Cardinal.mk I ≤ κ)
namespace DGGeneratedHomWord
variable (x y : (code R D κ a source target degree value coefficient hκ hI).Objects R κ)

def codeCochainLift (n : ℤ) (f : GradedHom R (value x) (value y) n)
    (hf : f ∈ linearSpan source target degree R D value coefficient x y n) : GradedHom R x y n := by
  letI := category source target degree R D value coefficient
  let L := codeToClosure R D κ a source target degree value coefficient hκ hI
  letI : IsIso (L.map x y) := codeToClosure_homIso R D κ a source target degree value coefficient hκ hI x y
  exact (inv (L.map x y)).f n ⟨f, hf⟩

lemma codeCochainLift_map (n : ℤ) (f : GradedHom R (value x) (value y) n)
    (hf : f ∈ linearSpan source target degree R D value coefficient x y n) :
    ((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).f n
      (codeCochainLift R D κ a source target degree value coefficient hκ hI x y n f hf) = f := by
  letI := category source target degree R D value coefficient
  let L := codeToClosure R D κ a source target degree value coefficient hκ hI
  letI : IsIso (L.map x y) := codeToClosure_homIso R D κ a source target degree value coefficient hκ hI x y
  change (inclusion source target degree R D value coefficient x y).f n
    ((L.map x y).f n ((inv (L.map x y)).f n ⟨f, hf⟩)) = f
  have h := congrArg (fun k => k.f n ⟨f, hf⟩) (IsIso.inv_hom_id (L.map x y))
  change (L.map x y).f n ((inv (L.map x y)).f n ⟨f, hf⟩) = ⟨f, hf⟩ at h
  rw [h]
  rfl

lemma codeEvaluation_degree_injective (n : ℤ) :
    Function.Injective (((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).f n) := by
  letI := category source target degree R D value coefficient
  let L := codeToClosure R D κ a source target degree value coefficient hκ hI
  letI : IsIso (L.map x y) := codeToClosure_homIso R D κ a source target degree value coefficient hκ hI x y
  haveI : IsIso ((L.map x y).f n) := by
    change IsIso ((HomologicalComplex.eval (ModuleCat R) (.up ℤ) n).map (L.map x y))
    infer_instance
  intro f g h
  apply (ModuleCat.mono_iff_injective ((L.map x y).f n)).1 inferInstance
  apply Subtype.ext
  exact h

lemma codeCochainLift_differential (n : ℤ) (f : GradedHom R (value x) (value y) n)
    (hf : f ∈ linearSpan source target degree R D value coefficient x y n)
    (hz : differential R f = 0) :
    differential R (codeCochainLift R D κ a source target degree value coefficient hκ hI x y n f hf) = 0 := by
  apply codeEvaluation_degree_injective R D κ a source target degree value coefficient hκ hI x y (n + 1)
  rw [map_zero]
  let g := codeCochainLift R D κ a source target degree value coefficient hκ hI x y n f hf
  have h := congrArg (fun k => k g)
    (((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).comm n (n + 1))
  change differential R (((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).f n g) =
    ((codeEvaluation R D κ a source target degree value coefficient hκ hI).map x y).f (n + 1) (differential R g) at h
  rw [← h, codeCochainLift_map]
  exact hz

end DGGeneratedHomWord
end SerrePositivity.DifferentialGraded

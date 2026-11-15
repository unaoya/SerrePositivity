module

public import SerrePositivity.AlgebraicGeometry.FiniteGeneratorSurjectivityLimit
public import SerrePositivity.AlgebraicGeometry.PushoutRingGenerators
public import Mathlib.RingTheory.FiniteType

/-!
概要：有限型の環写像の底変換の filtered 余極限での全射性を有限段へ降ろす。
方針：有限型性から生成元を選び、pushout の生成元と余極限の共通段の補題を使う。
規約：Stacks 07RH の可換環図式の形。余極限と pushout は実際の図式について仮定する。
使われ方：affine な閉埋め込み性の有限段への降下。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u

/-- 有限型の環写像には基底の像とともに環を生成する有限個の元がある。 -/
theorem exists_finset_ring_generators_of_finiteType
    {B C : CommRingCat.{u}} (g : B ⟶ C) (hg : g.hom.FiniteType) :
    ∃ s : Finset C, Subring.closure (Set.range g ∪ (s : Set C)) = ⊤ := by
  letI : Algebra B C := g.hom.toAlgebra
  letI : Algebra.FiniteType B C := hg
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := B) (A := C)
  refine ⟨s, ?_⟩
  change Subring.closure (Set.range (algebraMap B C) ∪ (s : Set C)) = ⊤
  rw [← Algebra.adjoin_eq_ring_closure]
  exact congrArg Subalgebra.toSubring hs

/-- 有限型の環写像の底変換の余極限で全射なら、ある有限段でも全射（Stacks 07RH）。 -/
theorem exists_surjective_stage_of_finiteType_pushouts
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (D E : J ⥤ CommRingCat.{u}) (τ : D ⟶ E)
    (cD : Cocone D) (cE : Cocone E) (hD : IsColimit cD) (hE : IsColimit cE)
    (φ : cD.pt ⟶ cE.pt) (hφ : Function.Surjective φ)
    (hcomm : ∀ j, cD.ι.app j ≫ φ = τ.app j ≫ cE.ι.app j)
    (i : J) (hfinite : (τ.app i).hom.FiniteType)
    (hpushout : ∀ (j : J) (f : i ⟶ j),
      IsPushout (τ.app i) (D.map f) (E.map f) (τ.app j)) :
    ∃ (j : J) (_ : i ⟶ j), Function.Surjective (τ.app j) := by
  classical
  obtain ⟨s, hs⟩ := exists_finset_ring_generators_of_finiteType (τ.app i) hfinite
  have hsrange : Set.range (fun a : s ↦ (a : E.obj i)) = (s : Set (E.obj i)) := by
    ext x
    simp
  apply exists_surjective_stage_of_uniform_generators D E τ cD cE hD hE φ hφ hcomm
    i (fun a : s ↦ (a : E.obj i))
  intro j f
  have h := closure_image_generators_eq_top_of_isPushout (hpushout j f).flip
    (Set.range (fun a : s ↦ (a : E.obj i))) (by simpa only [hsrange] using hs)
  simpa only [← Set.range_comp'] using h

end SerrePositivity.AlgebraicGeometry

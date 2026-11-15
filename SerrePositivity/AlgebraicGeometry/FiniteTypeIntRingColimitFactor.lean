module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Int.Basic

/-!
概要：有限型 ℤ-代数から filtered な環の colimit への写像を有限段へ因子化する。
方針：ULift ℤ を同じ宇宙の初期環にし、Noether 基底上の有限型から有限表示を得る。
規約：既存の有限表示環の colimit の因子化の係数移送。
使われ方：A07 の Noether 係数模型を整射の有限・有限表示段へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
universe u

set_option backward.isDefEq.respectTransparency false in
/-- 有限型 ℤ-代数から filtered な環の colimit への写像は、一つの段を通る。 -/
theorem exists_ringHom_factor_of_finiteType_int
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (A : Type u) [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]
    (g : A →+* c.pt) :
    ∃ (j : J) (g₀ : A →+* F.obj j), g = (c.ι.app j).hom.comp g₀ := by
  let Z := ULift.{u} ℤ
  let e : Z ≃+* ℤ := ULift.ringEquiv
  letI : IsNoetherianRing Z := isNoetherianRing_of_ringEquiv ℤ e.symm
  let f : CommRingCat.of Z ⟶ CommRingCat.of A :=
    CommRingCat.ofHom ((Int.castRingHom A).comp e.toRingHom)
  let α : (Functor.const J).obj (CommRingCat.of Z) ⟶ F :=
    { app := fun j ↦ CommRingCat.ofHom ((Int.castRingHom (F.obj j)).comp e.toRingHom)
      naturality := fun i j h ↦ by ext z; simp }
  have hfA : (Int.castRingHom A).FiniteType := by
    rw [← show algebraMap ℤ A = Int.castRingHom A from Subsingleton.elim _ _]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hf : f.hom.FinitePresentation :=
    RingHom.FinitePresentation.of_finiteType.mp
      (hfA.comp (RingHom.FiniteType.of_surjective e.toRingHom e.surjective))
  have hg : ∀ j, f ≫ CommRingCat.ofHom g = α.app j ≫ c.ι.app j := by
    intro j
    ext z
    simp [f, α]
  obtain ⟨j, g₀, _, heq⟩ := RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit
    (CommRingCat.of Z) F α f c hc hf (CommRingCat.ofHom g) hg
  exact ⟨j, g₀.hom, congrArg CommRingCat.Hom.hom heq⟩

end SerrePositivity.AlgebraicGeometry

module
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import Mathlib.Logic.Small.Set
public import Mathlib.SetTheory.Cardinal.Ordinal

/-!
概要：κ 未満自由 sphere の実小代表族と、射影的代表集合の導来 ∞ 比較を構成する。
方針：小さい ordinal 添字と実直和表示、β5 の全関手比較を保持する。
規約：全共変 Hom による κ-compact 性や全 κ-compact 被覆はここでは結論しない。
使われ方：K-7 に供給する実 κ-compact dg 小模型の出発点。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

abbrev DGKappaSphereFreeIndex (κ : Cardinal.{u}) :=
  Σ a : κ.ord.ToType, Set.Iio a → Shrink.{u} D × ℤ

abbrev dgKappaSphereFreeCells {κ : Cardinal.{u}} (i : DGKappaSphereFreeIndex D κ) :=
  ULift.{max u v, u} (Set.Iio i.1)

def dgKappaSphereFreeModule {κ : Cardinal.{u}} (i : DGKappaSphereFreeIndex D κ) :
    ModuleCategory R D :=
  ∐ (fun j : dgKappaSphereFreeCells D i ↦
    freeSphere R D ((equivShrink D).symm (i.2 j.down).1) (i.2 j.down).2)

def dgKappaSphereFreePresentation {κ : Cardinal.{u}} (i : DGKappaSphereFreeIndex D κ) :
    ModuleSphereFreePresentation R D (dgKappaSphereFreeModule R D i) where
  Index := dgKappaSphereFreeCells D i
  object j := (equivShrink D).symm (i.2 j.down).1
  degree j := (i.2 j.down).2
  iso := Iso.refl _

lemma dgKappaSphereFreeCells_card_lt {κ : Cardinal.{u}}
    (i : DGKappaSphereFreeIndex D κ) :
    Cardinal.mk (Shrink.{u} (dgKappaSphereFreeCells D i)) < κ := by
  have h := Cardinal.mk_congr
    ((equivShrink (dgKappaSphereFreeCells D i)).symm.trans Equiv.ulift)
  rw [h]
  simpa using (Cardinal.mk_Iio_lt i.1 (by simp))

lemma dgKappaSphereFreeModule_projective {κ : Cardinal.{u}}
    (i : DGKappaSphereFreeIndex D κ) :
    moduleHomotopicallyProjective R D (dgKappaSphereFreeModule R D i) :=
  (dgKappaSphereFreePresentation R D i).homotopicallyProjective R D

lemma dgKappaSphereFreeObjects_small (κ : Cardinal.{u}) :
    Small.{u} (Set.range (dgKappaSphereFreeModule R D (κ := κ))) := by infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories

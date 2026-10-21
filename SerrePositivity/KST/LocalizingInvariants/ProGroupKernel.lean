module

public import SerrePositivity.KST.LocalizingInvariants.ProSpectrumValues

/-!
概要：可換群の塔の核・余核の eventual 判定と、完全列の左 pro 零性からの核の零化。
方針：元のレベル射の自然性を完全列の持ち上げへ適用する。
規約：零化段は元に依存しない。使われ方：pro fiber 列から pro 同値を導く単射側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProGroup
open ProExcision

lemma zero_apply {A B : CommGrpCat.{u}} (x : A) : (0 : A ⟶ B).hom x = 1 := by
  let h := CommGrpCat.isZero_of_subsingleton (CommGrpCat.of PUnit.{u + 1})
  change (h.to_ B).hom ((h.from_ A).hom x) = 1
  have hx : (h.from_ A).hom x = 1 := Subsingleton.elim _ _
  rw [hx, map_one]

def IsEventuallyKernelTrivial {X Y : Tower CommGrpCat.{u}} (f : LevelHom X Y) : Prop :=
  ∀ n, ∃ m, ∃ h : n ≤ m, ∀ x : X.obj m,
    (f.app m).hom x = 1 → (X.transition h).hom x = 1

def IsEventuallyImageSurjective {X Y : Tower CommGrpCat.{u}} (f : LevelHom X Y) : Prop :=
  ∀ n, ∃ m, ∃ h : n ≤ m, ∀ y : Y.obj m,
    ∃ x : X.obj n, (f.app n).hom x = (Y.transition h).hom y

lemma eventuallyKernelTrivial_of_exact_proZero {A B C : Tower CommGrpCat.{u}}
    (i : LevelHom A B) (p : LevelHom B C)
    (hex : ∀ n (x : B.obj n), (p.app n).hom x = 1 ↔
      ∃ y : A.obj n, (i.app n).hom y = x)
    (hA : IsProZero A) : IsEventuallyKernelTrivial p := by
  intro n
  obtain ⟨m, h, hz⟩ := hA n
  refine ⟨m, h, fun x hx => ?_⟩
  obtain ⟨y, rfl⟩ := (hex m x).1 hx
  have hi := congrArg (fun t => t.hom y) (i.naturality h)
  change (i.app n).hom ((A.transition h).hom y) =
    (B.transition h).hom ((i.app m).hom y) at hi
  rw [hz, zero_apply, map_one] at hi
  exact hi.symm

end SerrePositivity.KST.LocalizingInvariants.ProGroup

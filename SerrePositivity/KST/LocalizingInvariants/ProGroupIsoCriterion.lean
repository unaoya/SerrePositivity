module

public import SerrePositivity.KST.LocalizingInvariants.ProGroupExactZero
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
概要：可換群の塔の核・余核の eventual 判定から、元の pro 同型判定を導く。
方針：核を消す遷移を像上へ降ろし、像に入る次の遷移と合成して群準同型の逆を作る。
規約：元の持ち上げに群準同型の切断を要求しない。使われ方：pro 長完全列の同値判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProGroup
open ProExcision

def descendRange {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]
    (f : A →* B) (g : A →* C) (h : f.ker ≤ g.ker) : f.range →* C :=
  (QuotientGroup.lift f.ker g h).comp (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom

lemma descendRange_apply {A B C : Type u} [CommGroup A] [CommGroup B] [CommGroup C]
    (f : A →* B) (g : A →* C) (h : f.ker ≤ g.ker) (x : A) (hx : f x ∈ f.range) :
    descendRange f g h ⟨f x, hx⟩ = g x := by
  have he : (QuotientGroup.quotientKerEquivRange f).symm ⟨f x, hx⟩ =
      QuotientGroup.mk x := by
    apply (QuotientGroup.quotientKerEquivRange f).injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  change (QuotientGroup.lift f.ker g h)
    ((QuotientGroup.quotientKerEquivRange f).symm ⟨f x, hx⟩) = _
  rw [he]
  rfl

lemma proIso_of_kernel_image {X Y : Tower CommGrpCat.{u}} {f : LevelHom X Y}
    (hm : IsEventuallyKernelTrivial f) (he : IsEventuallyImageSurjective f) : IsProIso f := by
  intro n
  obtain ⟨s, hns, hs⟩ := hm n
  obtain ⟨t, hst, ht⟩ := he s
  let a := (f.app s).hom
  let b := (X.transition hns).hom
  have hab : a.ker ≤ b.ker := by
    intro x hx
    exact hs x hx
  let q : Y.obj t →* a.range := (Y.transition hst).hom.codRestrict a.range (fun y => by
    obtain ⟨x, hx⟩ := ht y
    exact ⟨x, hx⟩)
  let g := (descendRange a b hab).comp q
  have value (y : Y.obj t) (x : X.obj s) (hx : a x = (Y.transition hst).hom y) :
      g y = b x := by
    change descendRange a b hab (q y) = b x
    have hq : q y = ⟨a x, ⟨x, rfl⟩⟩ := Subtype.ext hx.symm
    rw [hq]
    exact descendRange_apply a b hab x _
  refine ⟨t, hns.trans hst, CommGrpCat.ofHom g, ?_, ?_⟩
  · apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro x
    change g ((f.app t).hom x) = (X.transition (hns.trans hst)).hom x
    have hf : a ((X.transition hst).hom x) =
        (Y.transition hst).hom ((f.app t).hom x) :=
      congrArg (fun k => k.hom x) (f.naturality hst)
    rw [value _ _ hf]
    exact congrArg (fun k => k.hom x) (X.transition_comp hst hns)
  · apply CommGrpCat.hom_ext
    apply MonoidHom.ext
    intro y
    obtain ⟨x, hx⟩ := ht y
    change (f.app n).hom (g y) = (Y.transition (hns.trans hst)).hom y
    rw [value y x hx]
    have hf : (f.app n).hom (b x) = (Y.transition hns).hom (a x) :=
      congrArg (fun k => k.hom x) (f.naturality hns)
    rw [hf, hx]
    exact congrArg (fun k => k.hom y) (Y.transition_comp hst hns)

lemma kernelTrivial_of_proIso {X Y : Tower CommGrpCat.{u}} {f : LevelHom X Y}
    (hf : IsProIso f) : IsEventuallyKernelTrivial f := by
  intro n
  obtain ⟨m, h, g, hg, _⟩ := hf n
  refine ⟨m, h, fun x hx => ?_⟩
  have he := congrArg (fun k => k.hom x) hg
  change g.hom ((f.app m).hom x) = (X.transition h).hom x at he
  rw [hx, map_one] at he
  exact he.symm

lemma imageSurjective_of_proIso {X Y : Tower CommGrpCat.{u}} {f : LevelHom X Y}
    (hf : IsProIso f) : IsEventuallyImageSurjective f := by
  intro n
  obtain ⟨m, h, g, _, gh⟩ := hf n
  exact ⟨m, h, fun y => ⟨g.hom y, congrArg (fun k => k.hom y) gh⟩⟩

lemma proIso_iff_kernel_image {X Y : Tower CommGrpCat.{u}} (f : LevelHom X Y) :
    IsProIso f ↔ IsEventuallyKernelTrivial f ∧ IsEventuallyImageSurjective f :=
  ⟨fun h => ⟨kernelTrivial_of_proIso h, imageSurjective_of_proIso h⟩,
    fun h => proIso_of_kernel_image h.1 h.2⟩

lemma proIso_of_fourTerm_exact_proZero {A B C D : Tower CommGrpCat.{u}}
    (i : LevelHom A B) (p : LevelHom B C) (d : LevelHom C D)
    (hB : ∀ n (x : B.obj n), (p.app n).hom x = 1 ↔
      ∃ y : A.obj n, (i.app n).hom y = x)
    (hC : ∀ n (x : C.obj n), (d.app n).hom x = 1 ↔
      ∃ y : B.obj n, (p.app n).hom y = x)
    (hA : IsProZero A) (hD : IsProZero D) : IsProIso p :=
  proIso_of_kernel_image (eventuallyKernelTrivial_of_exact_proZero i p hB hA)
    (eventuallyImageSurjective_of_exact_proZero p d hC hD)

end SerrePositivity.KST.LocalizingInvariants.ProGroup

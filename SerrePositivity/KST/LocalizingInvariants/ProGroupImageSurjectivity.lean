module

public import SerrePositivity.KST.LocalizingInvariants.ProGroupIsoCriterion

/-!
概要：元の群の塔の eventual 像全射性を、合成の右辺と全射な比較正方形へ移す。
方針：元の像の持ち上げを成分へ送り、元のレベル射の自然性を使う。
規約：元に依存しない遷移段を保持。使われ方：像因子分解の新しい層の標的側判定。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProGroup
open ProExcision
variable {X Y Z : Tower CommGrpCat.{u}}

lemma kernelTrivial_of_levelwise_injective (f : LevelHom X Y)
    (hf : ∀ m, Function.Injective (f.app m).hom) : IsEventuallyKernelTrivial f := by
  intro n
  refine ⟨n, le_refl n, fun x hx => ?_⟩
  have he : x = 1 := hf n (hx.trans (map_one _).symm)
  rw [he, map_one]

lemma imageSurjective_right_of_comp (f : LevelHom X Y) (g : LevelHom Y Z)
    (h : IsEventuallyImageSurjective (f.comp g)) : IsEventuallyImageSurjective g := by
  intro n
  obtain ⟨m, hm, ht⟩ := h n
  refine ⟨m, hm, fun y => ?_⟩
  obtain ⟨x, hx⟩ := ht y
  exact ⟨(f.app n).hom x, hx⟩

lemma imageSurjective_of_square {X' Y' : Tower CommGrpCat.{u}}
    (f : LevelHom X Y) (f' : LevelHom X' Y') (a : LevelHom X X') (b : LevelHom Y Y')
    (hs : f.comp b = a.comp f') (hb : ∀ m, Function.Surjective (b.app m).hom)
    (hf : IsEventuallyImageSurjective f) : IsEventuallyImageSurjective f' := by
  intro n
  obtain ⟨m, hm, ht⟩ := hf n
  refine ⟨m, hm, fun y' => ?_⟩
  obtain ⟨y, hy⟩ := hb m y'
  obtain ⟨x, hx⟩ := ht y
  refine ⟨(a.app n).hom x, ?_⟩
  have hsq := congrArg (fun k => (k.app n).hom x) hs
  change (b.app n).hom ((f.app n).hom x) = (f'.app n).hom ((a.app n).hom x) at hsq
  have hn := congrArg (fun k => k.hom y) (b.naturality hm)
  change (b.app n).hom ((Y.transition hm).hom y) =
    (Y'.transition hm).hom ((b.app m).hom y) at hn
  exact hsq.symm.trans ((congrArg (b.app n).hom hx).trans
    (hn.trans (congrArg (Y'.transition hm).hom hy)))

lemma proIso_of_injective_and_eventual_image (f : LevelHom X Y)
    (hi : ∀ m, Function.Injective (f.app m).hom) (he : IsEventuallyImageSurjective f) :
    IsProIso f := proIso_of_kernel_image (kernelTrivial_of_levelwise_injective f hi) he

end SerrePositivity.KST.LocalizingInvariants.ProGroup

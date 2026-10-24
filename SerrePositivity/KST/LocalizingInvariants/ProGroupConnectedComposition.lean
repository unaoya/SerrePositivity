module

public import SerrePositivity.KST.LocalizingInvariants.ProGroupImageSurjectivity

/-!
概要：レベルごとの単射・全射と、後段の pro 同型から合成の eventual 核・像条件を導く。
方針：後段の一様な核零化段を使い、自然性と前段の単射で反映する。
規約：値の元に零化段を依存させない。使われ方：連結なレベル表示からの値の連結度。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.ProGroup
open ProExcision
variable {X Y Z : Tower CommGrpCat.{u}} (f : LevelHom X Y) (g : LevelHom Y Z)

lemma kernelTrivial_comp_of_injective (hf : ∀ i, Function.Injective (f.app i).hom)
    (hg : IsEventuallyKernelTrivial g) : IsEventuallyKernelTrivial (f.comp g) := by
  intro i
  obtain ⟨m, hi, hm⟩ := hg i
  refine ⟨m, hi, fun x hx => ?_⟩
  have hk := hm ((f.app m).hom x) hx
  have hn := congrArg (fun t => t.hom x) (f.naturality hi)
  change (f.app i).hom ((X.transition hi).hom x) =
    (Y.transition hi).hom ((f.app m).hom x) at hn
  exact hf i ((hn.trans hk).trans (map_one (f.app i).hom).symm)

lemma imageSurjective_comp_of_surjective (hf : ∀ i, Function.Surjective (f.app i).hom)
    (hg : IsEventuallyImageSurjective g) : IsEventuallyImageSurjective (f.comp g) := by
  intro i
  obtain ⟨m, hi, hm⟩ := hg i
  refine ⟨m, hi, fun z => ?_⟩
  obtain ⟨y, hy⟩ := hm z
  obtain ⟨x, hx⟩ := hf i y
  exact ⟨x, (congrArg (g.app i).hom hx).trans hy⟩

end SerrePositivity.KST.LocalizingInvariants.ProGroup

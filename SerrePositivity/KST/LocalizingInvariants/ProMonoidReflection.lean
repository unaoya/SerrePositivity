module

public import SerrePositivity.KST.LocalizingInvariants.ProTowerNatMap
public import Mathlib.CategoryTheory.Monoidal.Mon

/-!
概要：モノイド対象の忘却後の pro 同型から、元のモノイド対象の実 pro 逆を構成する。
方針：二段目の pro 逆で遷移を像に入れ、元の単位と積の保存式を回収する。
規約：積保存や逆の自然性を追加入力しない。使われ方：零 Postnikov 段の実代数比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory
open scoped MonObj
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {X Y : Tower (Mon C)} (f : LevelHom X Y)

lemma proIso_of_monoid_forget (hf : IsProIso (f.map (Mon.forget C))) : IsProIso f := by
  intro n
  obtain ⟨m, hn, g, hg, gh⟩ := hf n
  obtain ⟨k, hm, h, hh, hh'⟩ := hf m
  change (f.app m).hom ≫ g = (X.transition hn).hom at hg
  change g ≫ (f.app n).hom = (Y.transition hn).hom at gh
  change (f.app k).hom ≫ h = (X.transition hm).hom at hh
  change h ≫ (f.app m).hom = (Y.transition hm).hom at hh'
  let a := (Y.transition hm).hom ≫ g
  have ha : a = h ≫ (X.transition hn).hom := by
    dsimp only [a]
    rw [← hh', Category.assoc, hg]
  have hone : η[(Y.obj k).X] ≫ a = η[(X.obj n).X] := by
    calc
      _ = (η[(Y.obj m).X] ≫ g) := by
        dsimp only [a]
        rw [← Category.assoc, IsMonHom.one_hom]
      _ = (η[(X.obj m).X] ≫ (f.app m).hom) ≫ g := by
        rw [IsMonHom.one_hom (f.app m).hom]
      _ = η[(X.obj m).X] ≫ (X.transition hn).hom := by rw [Category.assoc, hg]
      _ = _ := IsMonHom.one_hom _
  have hmul : μ[(Y.obj k).X] ≫ a = (a ⊗ₘ a) ≫ μ[(X.obj n).X] := by
    calc
      _ = ((Y.transition hm).hom ⊗ₘ (Y.transition hm).hom) ≫ μ[(Y.obj m).X] ≫ g := by
        dsimp only [a]
        rw [← Category.assoc, IsMonHom.mul_hom, Category.assoc]
      _ = (h ⊗ₘ h) ≫ ((f.app m).hom ⊗ₘ (f.app m).hom) ≫ μ[(Y.obj m).X] ≫ g := by
        rw [← hh', ← tensorHom_comp_tensorHom, Category.assoc]
      _ = (h ⊗ₘ h) ≫ μ[(X.obj m).X] ≫ (X.transition hn).hom := by
        rw [← Category.assoc ((f.app m).hom ⊗ₘ (f.app m).hom) μ[(Y.obj m).X] g,
          ← IsMonHom.mul_hom (f.app m).hom, Category.assoc, hg]
      _ = (h ⊗ₘ h) ≫ ((X.transition hn).hom ⊗ₘ (X.transition hn).hom) ≫
          μ[(X.obj n).X] := by rw [IsMonHom.mul_hom]
      _ = (a ⊗ₘ a) ≫ μ[(X.obj n).X] := by
        rw [← Category.assoc, tensorHom_comp_tensorHom, ← ha]
  let b : Y.obj k ⟶ X.obj n := Mon.Hom.mk' a hone hmul
  refine ⟨k, hn.trans hm, b, ?_, ?_⟩
  · apply Mon.Hom.ext
    change (f.app k).hom ≫ a = (X.transition (hn.trans hm)).hom
    have he := congrArg (fun z => z.hom) (f.naturality hm)
    change (X.transition hm).hom ≫ (f.app m).hom =
      (f.app k).hom ≫ (Y.transition hm).hom at he
    dsimp only [a]
    rw [← Category.assoc, ← he, Category.assoc, hg, ← Mon.comp_hom', X.transition_comp]
  · apply Mon.Hom.ext
    change a ≫ (f.app n).hom = (Y.transition (hn.trans hm)).hom
    dsimp only [a]
    rw [Category.assoc, gh, ← Mon.comp_hom', Y.transition_comp]

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram

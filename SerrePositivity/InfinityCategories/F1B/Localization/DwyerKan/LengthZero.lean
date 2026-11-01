module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.LengthNaturality
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.WordUnit

/-!
# 元の長さ零の段階と空語の値の同型

概要：長さ零の全部分圏の余極限は、元の空語での値と同型である。
方針：長さ零の全語を空語と同定し、元の余極限余錐から逆射を構成する。
規約：逆射は元の空語の標準包含そのものである。
使われ方：全有限長さ段階の弱同値の帰納の基底。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

lemma Word.eq_empty_of_length_zero (a : Word) (h : a.length = 0) : a = Word.empty :=
  Word.object_ext a Word.empty h (fun i => Fin.elim0 (Fin.cast h i))

variable (F : Word ⥤ SSet.{w})

def lengthZeroCocone : Cocone (Word.lengthInclusion 0 ⋙ F) where
  pt := F.obj Word.empty
  ι :=
    { app a := F.map (eqToHom (Word.eq_empty_of_length_zero a.obj
        (Nat.eq_zero_of_le_zero a.property)))
      naturality a b f := by
        change F.map f.hom ≫ F.map (eqToHom _) = F.map (eqToHom _) ≫ 𝟙 _
        rw [Category.comp_id, ← CategoryTheory.Functor.map_comp]
        congr 1
        apply Word.hom_ext
        intro i
        exact Fin.elim0 (Fin.cast (Nat.eq_zero_of_le_zero a.property) i) }

def lengthZeroIso : lengthStage F 0 ≅ F.obj Word.empty where
  hom := colimit.desc _ (lengthZeroCocone F)
  inv := lengthStageInclusion F 0 Word.empty (le_refl 0)
  hom_inv_id := by
    apply colimit.hom_ext
    intro a
    rw [← Category.assoc, colimit.ι_desc]
    change F.map (eqToHom _) ≫ lengthStageInclusion F 0 Word.empty _ =
      lengthStageInclusion F 0 a.obj a.property ≫ 𝟙 _
    rw [Category.comp_id]
    exact lengthStageInclusion_naturality F 0 a.property (le_refl 0) _
  inv_hom_id := by
    change colimit.ι (Word.lengthInclusion 0 ⋙ F) ⟨Word.empty, le_refl 0⟩ ≫
      colimit.desc _ (lengthZeroCocone F) = 𝟙 _
    rw [colimit.ι_desc]
    change F.map (𝟙 Word.empty) = 𝟙 _
    exact CategoryTheory.Functor.map_id F Word.empty

lemma lengthZeroIso_inv : (lengthZeroIso F).inv =
    lengthStageInclusion F 0 Word.empty (le_refl 0) := rfl

end SerrePositivity.EInfinity.Hammock

module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.LengthStage

/-!
# 長さで制限した段階の元の Nat 図式

概要：長さの上限を増やす標準射を Nat 図式へ束ね、元の全語の余極限への余錐を得る。
方針：元の固定語の標準射上で恒等・合成・余錐の自然性を照合する。
規約：proper 性や段階の単射性は仮定しない。
使われ方：Dwyer–Kan §4.2 の実際の反復余極限。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

variable (F : Word ⥤ SSet.{w})

def lengthDiagram : ℕ ⥤ SSet.{w} where
  obj n := lengthStage F n
  map f := lengthStageTransition F (leOfHom f)
  map_id n := lengthStageTransition_refl F n
  map_comp f g := (lengthStageTransition_comp F (leOfHom f) (leOfHom g)).symm

def lengthStageToColimit (n : ℕ) : lengthStage F n ⟶ colimit F :=
  colimit.desc (Word.lengthInclusion n ⋙ F)
    { pt := colimit F
      ι :=
        { app a := colimit.ι F a.obj
          naturality a b f := by
            change F.map f.hom ≫ colimit.ι F b.obj = colimit.ι F a.obj ≫ 𝟙 _
            rw [Category.comp_id]
            exact colimit.w F f.hom } }

lemma lengthStageInclusion_toColimit (n : ℕ) (a : Word) (ha : a.length ≤ n) :
    lengthStageInclusion F n a ha ≫ lengthStageToColimit F n = colimit.ι F a :=
  colimit.ι_desc _ _

lemma lengthStageToColimit_transition {n m : ℕ} (h : n ≤ m) :
    lengthStageTransition F h ≫ lengthStageToColimit F m = lengthStageToColimit F n := by
  apply colimit.hom_ext
  intro a
  change lengthStageInclusion F n a.obj a.property ≫
    (lengthStageTransition F h ≫ lengthStageToColimit F m) =
    lengthStageInclusion F n a.obj a.property ≫ lengthStageToColimit F n
  rw [← Category.assoc, lengthStageInclusion_transition, lengthStageInclusion_toColimit,
    lengthStageInclusion_toColimit]

def lengthCocone : Cocone (lengthDiagram F) where
  pt := colimit F
  ι :=
    { app n := lengthStageToColimit F n
      naturality n m f := by
        change lengthStageTransition F (leOfHom f) ≫ lengthStageToColimit F m =
          lengthStageToColimit F n ≫ 𝟙 _
        rw [Category.comp_id]
        exact lengthStageToColimit_transition F (leOfHom f) }

end SerrePositivity.EInfinity.Hammock

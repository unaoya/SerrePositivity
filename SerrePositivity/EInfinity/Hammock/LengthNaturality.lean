module

public import SerrePositivity.EInfinity.Hammock.LengthColimit

/-!
# 長さ濾過の元の図式の比較に対する自然性

概要：元の自然変換は全長さ段階と Nat 図式に作用し、同じ元の余極限の射を回収する。
方針：全てを固定語の標準射で照合する。
規約：任意の同型で比較を代用せず、元の colim.map そのものへの一致を証明する。
使われ方：段階ごとの弱同値から元の全語の余極限の弱同値への移送。
-/

@[expose] public section
universe w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory CategoryTheory.Limits

variable {F G : Word ⥤ SSet.{w}} (η : F ⟶ G)

def lengthStageMap (n : ℕ) : lengthStage F n ⟶ lengthStage G n :=
  colim.map (Functor.whiskerLeft (Word.lengthInclusion n) η)

lemma lengthStageInclusion_map (n : ℕ) (a : Word) (ha : a.length ≤ n) :
    lengthStageInclusion F n a ha ≫ lengthStageMap η n =
      η.app a ≫ lengthStageInclusion G n a ha :=
  colimit.ι_map (Functor.whiskerLeft (Word.lengthInclusion n) η) ⟨a, ha⟩

lemma lengthStageMap_transition {n m : ℕ} (h : n ≤ m) :
    lengthStageMap η n ≫ lengthStageTransition G h =
      lengthStageTransition F h ≫ lengthStageMap η m := by
  apply colimit.hom_ext (F := Word.lengthInclusion n ⋙ F)
  intro a
  change lengthStageInclusion F n a.obj a.property ≫
    (lengthStageMap η n ≫ lengthStageTransition G h) =
    lengthStageInclusion F n a.obj a.property ≫
      (lengthStageTransition F h ≫ lengthStageMap η m)
  calc
    _ = η.app a.obj ≫ lengthStageInclusion G m a.obj (a.property.trans h) := by
      rw [← Category.assoc, lengthStageInclusion_map, Category.assoc,
        lengthStageInclusion_transition]
    _ = _ := by
      rw [← Category.assoc, lengthStageInclusion_transition, lengthStageInclusion_map]

def lengthDiagramMap : lengthDiagram F ⟶ lengthDiagram G where
  app n := lengthStageMap η n
  naturality _ _ f := (lengthStageMap_transition η (leOfHom f)).symm

lemma lengthStageToColimit_map (n : ℕ) :
    lengthStageMap η n ≫ lengthStageToColimit G n =
      lengthStageToColimit F n ≫ colim.map η := by
  apply colimit.hom_ext (F := Word.lengthInclusion n ⋙ F)
  intro a
  change lengthStageInclusion F n a.obj a.property ≫
    (lengthStageMap η n ≫ lengthStageToColimit G n) =
    lengthStageInclusion F n a.obj a.property ≫ (lengthStageToColimit F n ≫ colim.map η)
  calc
    _ = η.app a.obj ≫ colimit.ι G a.obj := by
      rw [← Category.assoc, lengthStageInclusion_map, Category.assoc,
        lengthStageInclusion_toColimit]
    _ = _ := by
      rw [← Category.assoc, lengthStageInclusion_toColimit, colimit.ι_map]

lemma lengthColimitIso_naturality :
    colim.map (lengthDiagramMap η) ≫ (lengthColimitIso G).hom =
      (lengthColimitIso F).hom ≫ colim.map η := by
  apply colimit.hom_ext (F := lengthDiagram F)
  intro n
  calc
    _ = lengthStageMap η n ≫ lengthStageToColimit G n := by
      rw [← Category.assoc, colimit.ι_map, Category.assoc, lengthColimitIso_fac]
      rfl
    _ = lengthStageToColimit F n ≫ colim.map η := lengthStageToColimit_map η n
    _ = _ := by rw [← Category.assoc, lengthColimitIso_fac]

end SerrePositivity.EInfinity.Hammock

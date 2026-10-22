module

public import SerrePositivity.KST.LocalizingInvariants.ProLevelwiseInverse

/-!
概要：元の通常自然同型を用いて、元の塔の射の実 pro 同型を移送する。
方針：元の全成分の同型と自然性の正方形を、既存の pro 比較へ渡す。
規約：元の射を変更しない。使われ方：層ホモロジーと元の群の比較。
-/

@[expose] public section
noncomputable section
universe u v u' v'
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {F G : C ⥤ D} (e : F ≅ G) {X Y : Tower C} (f : LevelHom X Y)

include e in
lemma proIso_of_natIso (hf : IsProIso (f.map F)) : IsProIso (f.map G) := by
  have : ∀ i, IsIso ((mapNat X e.hom).app i) := fun i => by
    change IsIso (e.hom.app (X.obj i))
    infer_instance
  have : ∀ i, IsIso ((mapNat Y e.hom).app i) := fun i => by
    change IsIso (e.hom.app (Y.obj i))
    infer_instance
  apply proIso_of_square (f.map F) (f.map G) (mapNat X e.hom) (mapNat Y e.hom) ?_ hf
  apply ProSpectrum.levelHom_ext
  intro i
  exact e.hom.naturality (f.app i)

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram

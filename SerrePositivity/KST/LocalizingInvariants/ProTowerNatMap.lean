module

public import SerrePositivity.KST.LocalizingInvariants.ProSpectrumValues

/-!
概要：実自然変換を既存の塔の実レベル射へ送り、元の成分と合成を保持する。
方針：元の自然性の四角形を Tower.map の遷移へ渡す。
規約：ProExcision は読み取り専用。使われ方：実 dg 因子分解の図式を pro 群へ送る。
-/

@[expose] public section
noncomputable section
universe u v u' v' u'' v''
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {F G H : C ⥤ D}

def mapNat (X : Tower C) (a : F ⟶ G) : LevelHom (X.map F) (X.map G) where
  app n := a.app (X.obj n)
  naturality h := a.naturality (X.transition h)

lemma mapNat_comp (X : Tower C) (a : F ⟶ G) (b : G ⟶ H) :
    mapNat X (a ≫ b) = (mapNat X a).comp (mapNat X b) := rfl

lemma mapNat_map (X : Tower C) (a : F ⟶ G) (L : D ⥤ E) :
    mapNat X (CategoryTheory.Functor.whiskerRight a L) = (mapNat X a).map L := rfl

lemma levelHom_map_comp {X Y Z : Tower C} (a : LevelHom X Y) (b : LevelHom Y Z) (L : C ⥤ D) :
    (a.comp b).map L = (a.map L).comp (b.map L) := by
  apply ProSpectrum.levelHom_ext
  intro n
  exact L.map_comp (a.app n) (b.app n)

lemma isProIso_of_levelwiseIso {X Y : Tower C} (f : LevelHom X Y) [∀ n, IsIso (f.app n)] :
    IsProIso f := by
  intro n
  refine ⟨n, le_refl n, inv (f.app n), ?_, ?_⟩
  · exact (IsIso.hom_inv_id _).trans (X.transition_self n).symm
  · exact (IsIso.inv_hom_id _).trans (Y.transition_self n).symm

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram

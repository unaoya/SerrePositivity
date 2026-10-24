module

public import SerrePositivity.KST.LocalizingInvariants.ProTowerNatMap

/-!
概要：実切断を持つレベル射の pro 逆から、元の切断自身の pro 逆を回収する。
方針：同じ段の射と遷移を逆候補とし、元の二つの逆三角形で検証する。
規約：一般 pro 圏の構成を要求しない。使われ方：対角射と元の射影の比較。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {X Y : Tower C}
  (s : LevelHom X Y) (r : LevelHom Y X) (hs : ∀ n, s.app n ≫ r.app n = 𝟙 _)

include hs in
lemma proIso_section_of_retraction (hr : IsProIso r) : IsProIso s := by
  intro n
  obtain ⟨m, h, a, ha, hb⟩ := hr n
  refine ⟨m, h, r.app m ≫ X.transition h, ?_, ?_⟩
  · rw [← Category.assoc, hs, Category.id_comp]
  · rw [Category.assoc, s.naturality, ← ha]
    rw [← Category.assoc (s.app m), hs, Category.id_comp]

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram

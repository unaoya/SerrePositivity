module

public import SerrePositivity.KST.LocalizingInvariants.ProTowerNatMap

/-!
概要：充満忠実な通常関手は、元の塔の pro 同型を反映する。
方針：元の eventual 逆射を充満性で戻し、二つの三角形を忠実性で反映する。
規約：元の添字と比較射を保持。使われ方：π₀ の加法・乗法表示の間の実 pro 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v u' v'
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

lemma proIso_of_fullyFaithful (F : C ⥤ D) [F.Full] [F.Faithful]
    {X Y : Tower C} (f : LevelHom X Y) (h : IsProIso (f.map F)) : IsProIso f := by
  intro n
  obtain ⟨m, hn, g, hg, gh⟩ := h n
  refine ⟨m, hn, F.preimage g, ?_, ?_⟩
  · apply F.map_injective
    rw [F.map_comp, F.map_preimage]
    exact hg
  · apply F.map_injective
    rw [F.map_comp, F.map_preimage]
    exact gh

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram

module

public import SerrePositivity.KST.LocalizingInvariants.ProTowerNatMap
public import Mathlib.CategoryTheory.Products.Basic

/-!
概要：二つの実関手で得た元の塔の pro 逆を、積圏に値を持つ元の塔の実逆にまとめる。
方針：二つの逆の添字の最大値を取り、元の遷移で二成分を同じ添字へ送る。
規約：一般 pro 圏は不要。使われ方：元の平方零標的の二つの座標の比較。
-/

@[expose] public section
noncomputable section
universe u v u' v' u'' v''
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E] {F : C ⥤ D} {G : C ⥤ E}
  {X Y : Tower C} (f : LevelHom X Y)

lemma proIso_prod' (hF : IsProIso (f.map F)) (hG : IsProIso (f.map G)) :
    IsProIso (f.map (F.prod' G)) := by
  intro i
  obtain ⟨m, hi, a, ha, ah⟩ := hF i
  obtain ⟨k, hk, b, hb, bh⟩ := hG i
  let p := max m k
  have hm : m ≤ p := le_max_left _ _
  have hn : k ≤ p := le_max_right _ _
  refine ⟨p, hi.trans hm, ((Y.map F).transition hm ≫ a, (Y.map G).transition hn ≫ b), ?_, ?_⟩
  · apply Prod.ext
    · change (f.map F).app p ≫ ((Y.map F).transition hm ≫ a) =
        (X.map F).transition (hi.trans hm)
      rw [← Category.assoc, ← (f.map F).naturality hm, Category.assoc, ha,
        (X.map F).transition_comp]
    · change (f.map G).app p ≫ ((Y.map G).transition hn ≫ b) =
        (X.map G).transition (hi.trans hm)
      rw [← Category.assoc, ← (f.map G).naturality hn, Category.assoc, hb,
        (X.map G).transition_comp]
  · apply Prod.ext
    · change ((Y.map F).transition hm ≫ a) ≫ (f.map F).app i =
        (Y.map F).transition (hi.trans hm)
      rw [Category.assoc, ah, (Y.map F).transition_comp]
    · change ((Y.map G).transition hn ≫ b) ≫ (f.map G).app i =
        (Y.map G).transition (hi.trans hm)
      rw [Category.assoc, bh, (Y.map G).transition_comp]

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram

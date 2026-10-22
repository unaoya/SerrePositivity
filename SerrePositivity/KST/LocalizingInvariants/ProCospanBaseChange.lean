module

public import SerrePositivity.KST.LocalizingInvariants.ProTowerNatMap
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan

/-!
概要：元の塔の pro 逆を、同じ中心・右脚を持つ元の cospan 図式の実 pro 逆へ上げる。
方針：左成分に元の逆、他の二成分に元の遷移を使い、二つの逆三角形を全成分で保つ。
規約：図式の逆の存在を入力しない。使われ方：零切断の逆による homotopy pullback 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {X Y Z : Tower C}
  (f : LevelHom X Y) (g : LevelHom Z Y)

def cospanTower : Tower (WalkingCospan ⥤ C) where
  obj i := cospan (f.app i) (g.app i)
  transition h := cospanHomMk (Y.transition h) (X.transition h) (Z.transition h)
    (f.naturality h).symm (g.naturality h).symm
  transition_self i := by
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact Y.transition_self i
    · exact X.transition_self i
    · exact Z.transition_self i
  transition_comp hm hn := by
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact Y.transition_comp hm hn
    · exact X.transition_comp hm hn
    · exact Z.transition_comp hm hn

def cospanBaseMap : LevelHom (cospanTower f g) (cospanTower (LevelHom.id Y) g) where
  app i := cospanHomMk (𝟙 (Y.obj i)) (f.app i) (𝟙 (Z.obj i))
    (by change f.app i ≫ 𝟙 _ = f.app i ≫ 𝟙 _; rfl)
    (by
      change g.app i ≫ 𝟙 _ = 𝟙 _ ≫ g.app i
      exact (Category.comp_id _).trans (Category.id_comp _).symm)
  naturality h := by
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact f.naturality h
    · exact (Category.comp_id _).trans (Category.id_comp _).symm

lemma cospanBaseMap_isProIso (hf : IsProIso f) : IsProIso (cospanBaseMap f g) := by
  intro n
  obtain ⟨m, hn, b, hb, bh⟩ := hf n
  let a : (cospanTower (LevelHom.id Y) g).obj m ⟶ (cospanTower f g).obj n :=
    cospanHomMk (Y.transition hn) b (Z.transition hn)
      (by
        change 𝟙 _ ≫ Y.transition hn = b ≫ f.app n
        simpa only [Category.id_comp] using bh.symm) (g.naturality hn).symm
  refine ⟨m, hn, a, ?_, ?_⟩
  · apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact Category.id_comp _
    · exact hb
    · exact Category.id_comp _
  · apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact Category.comp_id _
    · exact bh
    · exact Category.comp_id _

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram

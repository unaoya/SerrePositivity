module

public import SerrePositivity.KST.LocalizingInvariants.ProCospanBaseChange
public import SerrePositivity.KST.LocalizingInvariants.ProFiniteDiagramReflection

/-!
概要：元の cospan 図式の射を、左対象を固定する射と左対象だけを変える射へ分解する。
方針：元の左成分を標的の左脚へ前合成し、三成分で元の合成と自然性を保つ。
規約：中心・右成分の実 pro 同型から第一射の図式全体の実逆を構成する。
使われ方：class 図式の左準同型と中心・右の pro 逆の分離。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits WalkingCospan WalkingCospan.Hom
namespace SerrePositivity.KST.LocalizingInvariants.TowerDiagram
open ProExcision
variable {C : Type u} [Category.{v} C] {X Y : Tower (WalkingCospan ⥤ C)} (f : LevelHom X Y)

abbrev cospanEval (j : WalkingCospan) := (CategoryTheory.evaluation WalkingCospan C).obj j

def sourceFactorLeft : LevelHom (X.map (cospanEval .left)) (Y.map (cospanEval .one)) :=
  (f.map (cospanEval .left)).comp (mapNat Y ((CategoryTheory.evaluation _ _).map inl))

def sourceFactorRight : LevelHom (Y.map (cospanEval .right)) (Y.map (cospanEval .one)) :=
  mapNat Y ((CategoryTheory.evaluation _ _).map inr)

def sourceFactorTower : Tower (WalkingCospan ⥤ C) :=
  cospanTower (sourceFactorLeft f) (sourceFactorRight (Y := Y))

def sourceFactorFirst : LevelHom X (sourceFactorTower f) where
  app i := cospanHomMk ((f.app i).app .one) (𝟙 _) ((f.app i).app .right)
    (by
      change (X.obj i).map inl ≫ (f.app i).app .one =
        𝟙 _ ≫ ((f.app i).app .left ≫ (Y.obj i).map inl)
      rw [Category.id_comp]
      exact (f.app i).naturality inl)
    ((f.app i).naturality inr)
  naturality h := by
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact congrArg (fun t => t.app .one) (f.naturality h)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact congrArg (fun t => t.app .right) (f.naturality h)

def sourceFactorSecond : LevelHom (sourceFactorTower f) Y where
  app i := cospanHomMk (𝟙 _) ((f.app i).app .left) (𝟙 _)
    (by
      change ((f.app i).app .left ≫ (Y.obj i).map inl) ≫ 𝟙 _ =
        (f.app i).app .left ≫ (Y.obj i).map inl
      exact Category.comp_id _)
    (by
      change (Y.obj i).map inr ≫ 𝟙 _ = 𝟙 _ ≫ (Y.obj i).map inr
      simp)
  naturality h := by
    apply NatTrans.ext
    funext j
    rcases j with _ | (_ | _)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact congrArg (fun t => t.app .left) (f.naturality h)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm

lemma sourceFactor_fac : (sourceFactorFirst f).comp (sourceFactorSecond f) = f := by
  apply ProSpectrum.levelHom_ext
  intro i
  apply NatTrans.ext
  funext j
  rcases j with _ | (_ | _)
  · exact Category.comp_id _
  · exact Category.id_comp _
  · exact Category.comp_id _

lemma sourceFactorFirst_isProIso
    (hC : IsProIso (f.map (cospanEval .one)))
    (hR : IsProIso (f.map (cospanEval .right))) : IsProIso (sourceFactorFirst f) := by
  apply proIso_of_pointwise
  intro j
  rcases j with _ | (_ | _)
  · exact hC
  · have : ∀ i, IsIso (((sourceFactorFirst f).map (cospanEval .left)).app i) := by
      intro i
      change IsIso (𝟙 ((X.obj i).obj .left))
      infer_instance
    exact isProIso_of_levelwiseIso _
  · exact hR

end SerrePositivity.KST.LocalizingInvariants.TowerDiagram

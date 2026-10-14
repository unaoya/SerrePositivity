module

public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroInternalHomNaturality
public import SerrePositivity.Spectra.SymmetricSequence.FreeInternalHomModuleNaturality

/-! # 自由零生成加群の比較の下での射の前合成・後合成の法則 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]

/-- 通常の内部Homの対称列の射が、各段の前合成・後合成になるという法則。 -/
def unshiftedInternalHomMapLaw {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G)
    (h : unshiftedInternalHom Y F ⟶ unshiftedInternalHom X G) : Prop :=
  h = unshiftedInternalHomMap f g

omit [SymmetricCategory C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)] in
/-- 対称列全体の射の法則から、各段の通常の前合成・後合成の公式を得る。 -/
lemma unshiftedInternalHomMapLaw_app {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G)
    (h : unshiftedInternalHom Y F ⟶ unshiftedInternalHom X G) (q : ℕ)
    (hh : unshiftedInternalHomMapLaw f g h) :
    h.app (FiniteBijection.of q) =
      (pre f).app (level F q) ≫ (ihom X).map (g.app (FiniteBijection.of q)) := by
  change h = unshiftedInternalHomMap f g at hh
  rw [hh, unshiftedInternalHomMap_app]

/-- 通常の内部Homの射の第q段が、前合成・後合成の公式になるという法則。 -/
def unshiftedInternalHomMapLevelLaw {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G)
    (h : unshiftedInternalHom Y F ⟶ unshiftedInternalHom X G) (q : ℕ) : Prop :=
  h.app (FiniteBijection.of q) =
    (pre f).app (level F q) ≫ (ihom X).map (g.app (FiniteBijection.of q))

omit [SymmetricCategory C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)] in
/-- 対称列全体の前合成・後合成の法則は、各段の法則を与える。 -/
lemma unshiftedInternalHomMapLaw_levelLaw {X Y : C} (f : X ⟶ Y)
    {F G : SymmetricSequence C} (g : F ⟶ G)
    (h : unshiftedInternalHom Y F ⟶ unshiftedInternalHom X G) (q : ℕ)
    (hh : unshiftedInternalHomMapLaw f g h) :
    unshiftedInternalHomMapLevelLaw f g h q :=
  unshiftedInternalHomMapLaw_app f g h q hh

variable (M : SymmetricSequence C) [MonObj M] [IsCommMonObj M]

/-- 二つの係数加群の比較で移した内部Homの射の基礎射を計算する。 -/
lemma freeZeroModuleMap_hom {X Y : C} (f : X ⟶ Y)
    {F G A B : Mod (SymmetricSequence C) M} (g : F ⟶ G)
    (s : MonoidalModuleInternalHom.moduleObj M
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj Y)) F ≅ A)
    (t : MonoidalModuleInternalHom.moduleObj M
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) G ≅ B)
    (e : (ihom ((freeAt 0).obj Y)).obj F.X ≅ A.X)
    (d : (ihom ((freeAt 0).obj X)).obj G.X ≅ B.X)
    (hs : s.inv.hom = e.inv ≫ (MonoidalModuleInternalHom.freeHomIso M ((freeAt 0).obj Y) F).inv)
    (ht : t.hom.hom = (MonoidalModuleInternalHom.freeHomIso M ((freeAt 0).obj X) G).hom ≫ d.hom) :
    (s.inv ≫ MonoidalModuleInternalHom.homMap M
        (MonoidalFreeModule.freeMap M ((freeAt 0).map f)) g ≫ t.hom).hom =
      e.inv ≫ (pre ((freeAt 0).map f)).app F.X ≫
        (ihom ((freeAt 0).obj X)).map g.hom ≫ d.hom := by
  simp only [Mod.comp_hom', hs, ht, Category.assoc]
  have hp := MonoidalModuleInternalHom.freeHomMap_hom M ((freeAt 0).map f) g
  change (MonoidalModuleInternalHom.freeHomIso M ((freeAt 0).obj Y) F).inv ≫
      (MonoidalModuleInternalHom.homMap M
        (MonoidalFreeModule.freeMap M ((freeAt 0).map f)) g).hom ≫
          (MonoidalModuleInternalHom.freeHomIso M ((freeAt 0).obj X) G).hom = _ at hp
  have hp' := congrArg (fun k => e.inv ≫ k ≫ d.hom) hp
  simpa only [Category.assoc] using hp'

/-- 全体の比較の順逆と両立する加群射は、通常の前合成・後合成の法則を満たす。 -/
lemma freeZeroModuleMap_law {X Y : C} (f : X ⟶ Y)
    {F G A B : Mod (SymmetricSequence C) M} (g : F ⟶ G)
    (s : MonoidalModuleInternalHom.moduleObj M
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj Y)) F ≅ A)
    (t : MonoidalModuleInternalHom.moduleObj M
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) G ≅ B)
    (h : A ⟶ B)
    (e : (ihom ((freeAt 0).obj Y)).obj F.X ≅ unshiftedInternalHom Y F.X)
    (d : (ihom ((freeAt 0).obj X)).obj G.X ≅ unshiftedInternalHom X G.X)
    (a : A.X ≅ unshiftedInternalHom Y F.X) (b : B.X ≅ unshiftedInternalHom X G.X)
    (hs : s.inv.hom = a.hom ≫ e.inv ≫
      (MonoidalModuleInternalHom.freeHomIso M ((freeAt 0).obj Y) F).inv)
    (ht : t.hom.hom = (MonoidalModuleInternalHom.freeHomIso M ((freeAt 0).obj X) G).hom ≫
      d.hom ≫ b.inv)
    (hh : s.inv ≫ MonoidalModuleInternalHom.homMap M
      (MonoidalFreeModule.freeMap M ((freeAt 0).map f)) g ≫ t.hom = h)
    (he : e.inv = (freeZeroInternalHomNatIso Y).inv.app F.X)
    (hd : d.hom = (freeZeroInternalHomNatIso X).hom.app G.X) :
    unshiftedInternalHomMapLaw f g.hom (a.inv ≫ h.hom ≫ b.hom) := by
  unfold unshiftedInternalHomMapLaw
  rw [← hh]
  have hp := freeZeroModuleMap_hom M f g s t (e ≪≫ a.symm) (d ≪≫ b.symm)
    (by simpa only [Iso.trans_inv, Iso.symm_inv, Category.assoc] using hs)
    (by simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using ht)
  rw [hp]
  simp only [Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [he, hd]
  exact freeZeroInternalHomNatIso_conjugate f g.hom

end SerrePositivity.SymmetricSequence

module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictRawModules

/-!
# 元の BE 加群制限の比較の貼り合わせ

概要：HA §4.2.3 の元の制限の単位・合成比較を、同じ成分で貼り合わせる。
方針：唯一点での忠実な評価により、各比較の成分が恒等であることを使う。
規約：任意に選んだ同型で置き換えない。使われ方：M10 の厳密な相対族の構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory CategoryTheory.Functor
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {A : Type u} [CommRing A]

/-- 概要：元の制限は同じ台の射を保持する（HA §4.2.3）。
方針：既存の制限の評価式を唯一点に適用する。
規約：同じ鎖写像。使われ方：比較の貼り合わせの評価。 -/
lemma strictRawModuleRestrict_eval {X Y : (operad A).Algebra} (f : X ⟶ Y)
    {M T : strictRawModuleCategory A Y} (g : M ⟶ T) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict f).map g) =
      (strictRawModuleUnderlying Y).map g := by
  unfold strictRawModuleUnderlying strictRawModuleRestrict
  rw [moduleRestriction_map_eval]

/-- 概要：単位比較の逆も同じ台で恒等（HA §4.2.3）。
方針：同じ比較の両逆則を評価する。
規約：元の逆成分。使われ方：相対族の単位の向きの変更。 -/
lemma strictRawModuleRestrict_idIso_inv_eval (X : (operad A).Algebra)
    (M : strictRawModuleCategory A X) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_idIso X).inv.app M) =
      𝟙 ((strictRawModuleUnderlying X).obj M) := by
  have hi := congrArg (strictRawModuleUnderlying X).map
    (((strictRawModuleRestrict_idIso X).app M).hom_inv_id)
  rw [CategoryTheory.Functor.map_comp, Iso.app_hom, Iso.app_inv,
    strictRawModuleRestrict_idIso_eval, CategoryTheory.Functor.map_id] at hi
  change 𝟙 ((strictRawModuleUnderlying X).obj M) ≫
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_idIso X).inv.app M) =
      𝟙 ((strictRawModuleUnderlying X).obj M) at hi
  simpa only [Category.id_comp] using hi

/-- 概要：合成比較の逆も同じ台で恒等（HA §4.2.3）。
方針：同じ比較の両逆則を評価する。
規約：元の逆成分。使われ方：相対族の結合の向きの変更。 -/
lemma strictRawModuleRestrict_compIso_inv_eval {X Y Z : (operad A).Algebra}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : strictRawModuleCategory A Z) :
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_compIso f g).inv.app M) =
      𝟙 ((strictRawModuleUnderlying Z).obj M) := by
  have hi := congrArg (strictRawModuleUnderlying X).map
    (((strictRawModuleRestrict_compIso f g).app M).hom_inv_id)
  rw [CategoryTheory.Functor.map_comp, Iso.app_hom, Iso.app_inv,
    strictRawModuleRestrict_compIso_eval, CategoryTheory.Functor.map_id] at hi
  change 𝟙 ((strictRawModuleUnderlying Z).obj M) ≫
    (strictRawModuleUnderlying X).map ((strictRawModuleRestrict_compIso f g).inv.app M) =
      𝟙 ((strictRawModuleUnderlying Z).obj M) at hi
  simpa only [Category.id_comp] using hi

/-- 概要：制限の合成比較は同じ三つの射に関して結合的（HA §4.2.3）。
方針：比較を唯一点で評価し、恒等成分の合成として照合する。
規約：元の合成比較。使われ方：相対 Grothendieck 構成の結合則。 -/
lemma strictRawModuleRestrict_comp_assoc {W X Y Z : (operad A).Algebra}
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    isoWhiskerRight (strictRawModuleRestrict_compIso g h) (strictRawModuleRestrict f) ≪≫
        strictRawModuleRestrict_compIso f (g ≫ h) =
      Functor.associator (strictRawModuleRestrict h) (strictRawModuleRestrict g)
          (strictRawModuleRestrict f) ≪≫
        isoWhiskerLeft (strictRawModuleRestrict h) (strictRawModuleRestrict_compIso f g) ≪≫
        strictRawModuleRestrict_compIso (f ≫ g) h ≪≫
        eqToIso (congrArg (fun k => strictRawModuleRestrict k) (Category.assoc f g h)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply strictRawModuleHom_ext
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Functor.associator_hom_app,
    eqToIso.hom, eqToHom_app, eqToHom_map, CategoryTheory.Functor.map_comp,
    strictRawModuleRestrict_compIso_eval, strictRawModuleRestrict_eval,
    Category.id_comp]
  change (𝟙 ((strictRawModuleUnderlying Z).obj M) ≫ 𝟙 _) = (𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _)
  simp only [Category.id_comp]

/-- 概要：終点の恒等制限と合成比較は同じ単位比較（HA §4.2.3）。
方針：唯一点の忠実性で同じ恒等成分を照合する。
規約：元の単位比較。使われ方：相対族の左単位則。 -/
lemma strictRawModuleRestrict_comp_id {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleRestrict_compIso f (𝟙 Y) ≪≫
        eqToIso (congrArg (fun k => strictRawModuleRestrict k) (Category.comp_id f)) =
      isoWhiskerRight (strictRawModuleRestrict_idIso Y) (strictRawModuleRestrict f) ≪≫
        Functor.leftUnitor (strictRawModuleRestrict f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply strictRawModuleHom_ext
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    Functor.leftUnitor_hom_app, eqToIso.hom, eqToHom_app, CategoryTheory.Functor.map_comp,
    strictRawModuleRestrict_compIso_eval, strictRawModuleRestrict_idIso_eval,
    strictRawModuleRestrict_eval]
  rfl

/-- 概要：始点の恒等制限と合成比較は同じ単位比較（HA §4.2.3）。
方針：唯一点の忠実性で同じ恒等成分を照合する。
規約：元の単位比較。使われ方：相対族の右単位則。 -/
lemma strictRawModuleRestrict_id_comp {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictRawModuleRestrict_compIso (𝟙 X) f ≪≫
        eqToIso (congrArg (fun k => strictRawModuleRestrict k) (Category.id_comp f)) =
      isoWhiskerLeft (strictRawModuleRestrict f) (strictRawModuleRestrict_idIso X) ≪≫
        Functor.rightUnitor (strictRawModuleRestrict f) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply strictRawModuleHom_ext
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom, whiskerLeft_app,
    Functor.rightUnitor_hom_app, eqToIso.hom, eqToHom_app, CategoryTheory.Functor.map_comp,
    strictRawModuleRestrict_compIso_eval, strictRawModuleRestrict_idIso_eval,
    Category.comp_id]
  rfl

end SerrePositivity.EInfinity.BarrattEccles

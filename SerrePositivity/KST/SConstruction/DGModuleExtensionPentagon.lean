module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionFourfold
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputCoherence

/-! # 実加群延長の四重比較
概要：左結合から右結合への元の四重比較を、入力等号移送を保って照合する。
方針：外側の三重比較、閉零自然性、内側の三重比較を順に合成する。
規約：元の合成比較を置き換えない。使われ方：四入力五角の両経路の正規化。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z q r
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A]
  (D : Type v) (E : Type w) (T : Type z) (U : Type q) (V : Type r)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] [DGCategory A U] [Small.{u} U]
  [DGCategory A V] [Small.{u} V]
  (F : DGFunctor A D E) (G : DGFunctor A E T)
  (H : DGFunctor A T U) (I : DGFunctor A U V) (M : RightModule A D)

/-- 左結合と右結合の四重比較は、三つの元の結合等号移送を保って一致する。 -/
lemma dgModuleExtensionCompositionAt_fourfold_long :
    (dgModuleExtension A U V I).onClosed.map
        ((dgModuleExtension A T U H).onClosed.map
          (dgModuleExtensionCompositionAt A D E T F G M).hom) ≫
      (dgModuleExtension A U V I).onClosed.map
        (dgModuleExtensionCompositionAt A D T U (F.comp G) H M).hom ≫
      (dgModuleExtensionCompositionAt A D U V ((F.comp G).comp H) I M).hom ≫
      (dgModuleExtensionInputIso A D V
        (F := ((F.comp G).comp H).comp I) (G := (F.comp (G.comp H)).comp I)
        (congrArg (fun K => K.comp I) (strictDGFunctor_comp_assoc F G H)) M).hom ≫
      (dgModuleExtensionInputIso A D V
        (strictDGFunctor_comp_assoc F (G.comp H) I) M).hom ≫
      (dgModuleExtensionInputIso A D V
        (F := F.comp ((G.comp H).comp I)) (G := F.comp (G.comp (H.comp I)))
        (congrArg (fun K => F.comp K) (strictDGFunctor_comp_assoc G H I)) M).hom =
    (dgModuleExtensionCompositionAt A T U V H I
        ((dgModuleExtension A E T G).obj ((dgModuleExtension A D E F).obj M))).hom ≫
      (dgModuleExtensionCompositionAt A E T V G (H.comp I)
        ((dgModuleExtension A D E F).obj M)).hom ≫
      (dgModuleExtensionCompositionAt A D E V F (G.comp (H.comp I)) M).hom := by
  let a := (strictDGFunctor_comp_assoc F G H)
  let b := strictDGFunctor_comp_assoc F (G.comp H) I
  let c := strictDGFunctor_comp_assoc G H I
  have hi := dgModuleExtensionCompositionAt_input_left A D U V a I M
  have hm := congrArg ((dgModuleExtension A U V I).onClosed.map)
    (dgModuleExtensionCompositionAt_assoc A D E T U F G H M)
  simp only [CategoryTheory.Functor.map_comp] at hm
  have hb := dgModuleExtensionCompositionAt_assoc A D E U V F (G.comp H) I M
  have hc := dgModuleExtensionCompositionAt_input_right A D E V F c M
  have ht := dgModuleExtensionCompositionAt_assoc A E T U V G H I
    ((dgModuleExtension A D E F).obj M)
  have hi' := congrArg (fun k =>
    (dgModuleExtension A U V I).onClosed.map
        ((dgModuleExtension A T U H).onClosed.map
          (dgModuleExtensionCompositionAt A D E T F G M).hom) ≫
      (dgModuleExtension A U V I).onClosed.map
        (dgModuleExtensionCompositionAt A D T U (F.comp G) H M).hom ≫ k ≫
      (dgModuleExtensionInputIso A D V b M).hom ≫
      (dgModuleExtensionInputIso A D V
        (F := F.comp ((G.comp H).comp I)) (G := F.comp (G.comp (H.comp I)))
        (congrArg (fun K => F.comp K) c) M).hom) hi.symm
  have hm' := congrArg (fun k => k ≫
    (dgModuleExtensionCompositionAt A D U V (F.comp (G.comp H)) I M).hom ≫
      (dgModuleExtensionInputIso A D V b M).hom ≫
      (dgModuleExtensionInputIso A D V
        (F := F.comp ((G.comp H).comp I)) (G := F.comp (G.comp (H.comp I)))
        (congrArg (fun K => F.comp K) c) M).hom) hm
  have hb' := congrArg (fun k =>
    (dgModuleExtension A U V I).onClosed.map
        (dgModuleExtensionCompositionAt A E T U G H
          ((dgModuleExtension A D E F).obj M)).hom ≫ k ≫
      (dgModuleExtensionInputIso A D V
        (F := F.comp ((G.comp H).comp I)) (G := F.comp (G.comp (H.comp I)))
        (congrArg (fun K => F.comp K) c) M).hom) hb
  have hc' := congrArg (fun k =>
    (dgModuleExtension A U V I).onClosed.map
        (dgModuleExtensionCompositionAt A E T U G H
          ((dgModuleExtension A D E F).obj M)).hom ≫
      (dgModuleExtensionCompositionAt A E U V (G.comp H) I
        ((dgModuleExtension A D E F).obj M)).hom ≫ k) hc.symm
  have ht' := congrArg (fun k => k ≫
    (dgModuleExtensionCompositionAt A D E V F (G.comp (H.comp I)) M).hom) ht
  simp only [Category.assoc] at hi' hm' hb' hc' ht'
  exact hi'.trans (hm'.trans (hb'.trans (hc'.trans ht')))

/-- 元の四重比較からの五角の長経路と短経路は、全入力移送を保って一致する。 -/
lemma dgModuleExtensionCompositionAt_pentagon :
    (dgModuleExtension A U V I).onClosed.map
        ((dgModuleExtension A T U H).onClosed.map
          (dgModuleExtensionCompositionAt A D E T F G M).hom) ≫
      (dgModuleExtension A U V I).onClosed.map
        (dgModuleExtensionCompositionAt A D T U (F.comp G) H M).hom ≫
      (dgModuleExtensionCompositionAt A D U V ((F.comp G).comp H) I M).hom ≫
      (dgModuleExtensionInputIso A D V
        (F := ((F.comp G).comp H).comp I) (G := (F.comp (G.comp H)).comp I)
        (congrArg (fun K => K.comp I) (strictDGFunctor_comp_assoc F G H)) M).hom ≫
      (dgModuleExtensionInputIso A D V
        (strictDGFunctor_comp_assoc F (G.comp H) I) M).hom ≫
      (dgModuleExtensionInputIso A D V
        (F := F.comp ((G.comp H).comp I)) (G := F.comp (G.comp (H.comp I)))
        (congrArg (fun K => F.comp K) (strictDGFunctor_comp_assoc G H I)) M).hom =
    (dgModuleExtension A U V I).onClosed.map
        ((dgModuleExtension A T U H).onClosed.map
          (dgModuleExtensionCompositionAt A D E T F G M).hom) ≫
      (dgModuleExtension A U V I).onClosed.map
        (dgModuleExtensionCompositionAt A D T U (F.comp G) H M).hom ≫
      (dgModuleExtensionCompositionAt A D U V ((F.comp G).comp H) I M).hom ≫
      (dgModuleExtensionInputIso A D V
        (strictDGFunctor_comp_assoc (F.comp G) H I) M).hom ≫
      (dgModuleExtensionInputIso A D V
        (strictDGFunctor_comp_assoc F G (H.comp I)) M).hom := by
  exact (dgModuleExtensionCompositionAt_fourfold_long A D E T U V F G H I M).trans
    (dgModuleExtensionCompositionAt_fourfold A D E T U V F G H I M).symm

end SerrePositivity.KST.SConstruction

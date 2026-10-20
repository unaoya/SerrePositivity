module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionClosedNaturality
public import SerrePositivity.KST.SConstruction.DGModuleExtensionTripleEvaluation

/-! # 実加群延長の四重比較
概要：左結合から右結合への元の四重比較を、入力等号移送を保って照合する。
方針：外側の三重比較、閉零自然性、内側の三重比較を順に合成する。
規約：元の合成比較を置き換えない。使われ方：四入力五角の二辺側の正規化。
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

/-- 左結合と右結合の四重比較は、二つの元の結合等号移送を保って一致する。 -/
lemma dgModuleExtensionCompositionAt_fourfold :
    (dgModuleExtension A U V I).onClosed.map
        ((dgModuleExtension A T U H).onClosed.map
          (dgModuleExtensionCompositionAt A D E T F G M).hom) ≫
      (dgModuleExtension A U V I).onClosed.map
        (dgModuleExtensionCompositionAt A D T U (F.comp G) H M).hom ≫
      (dgModuleExtensionCompositionAt A D U V ((F.comp G).comp H) I M).hom ≫
      (dgModuleExtensionInputIso A D V
        (strictDGFunctor_comp_assoc (F.comp G) H I) M).hom ≫
      (dgModuleExtensionInputIso A D V
        (strictDGFunctor_comp_assoc F G (H.comp I)) M).hom =
    (dgModuleExtensionCompositionAt A T U V H I
        ((dgModuleExtension A E T G).obj ((dgModuleExtension A D E F).obj M))).hom ≫
      (dgModuleExtensionCompositionAt A E T V G (H.comp I)
        ((dgModuleExtension A D E F).obj M)).hom ≫
      (dgModuleExtensionCompositionAt A D E V F (G.comp (H.comp I)) M).hom := by
  have h₁ := dgModuleExtensionCompositionAt_assoc A D T U V (F.comp G) H I M
  have hn := dgModuleExtensionCompositionAt_closed_naturality A T U V H I
    (dgModuleExtensionCompositionAt A D E T F G M).hom
  have h₂ := dgModuleExtensionCompositionAt_assoc A D E T V F G (H.comp I) M
  have h₁' := congrArg (fun k =>
    (dgModuleExtension A U V I).onClosed.map
        ((dgModuleExtension A T U H).onClosed.map
          (dgModuleExtensionCompositionAt A D E T F G M).hom) ≫ k ≫
      (dgModuleExtensionInputIso A D V
        (strictDGFunctor_comp_assoc F G (H.comp I)) M).hom) h₁
  have hn' := congrArg (fun k => k ≫
    (dgModuleExtensionCompositionAt A D T V (F.comp G) (H.comp I) M).hom ≫
      (dgModuleExtensionInputIso A D V
        (strictDGFunctor_comp_assoc F G (H.comp I)) M).hom) hn
  have h₂' := congrArg (fun k =>
    (dgModuleExtensionCompositionAt A T U V H I
      ((dgModuleExtension A E T G).obj ((dgModuleExtension A D E F).obj M))).hom ≫ k) h₂
  simp only [Category.assoc] at h₁' hn' h₂'
  exact h₁'.trans (hn'.trans h₂')

end SerrePositivity.KST.SConstruction

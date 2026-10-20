module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionFourfold
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionAssociativity

/-! # 実 Perf 延長の四重比較
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
  (H : DGFunctor A T U) (I : DGFunctor A U V) (M : PerfectDGModule A D)

/-- 左結合と右結合の四重比較は、二つの元の結合等号移送を保って一致する。 -/
lemma perfectDGExtensionCompositionAt_fourfold :
    (perfectDGExtension A U V I).onClosed.map
        ((perfectDGExtension A T U H).onClosed.map
          (perfectDGExtensionCompositionAt A D E T F G M).hom) ≫
      (perfectDGExtension A U V I).onClosed.map
        (perfectDGExtensionCompositionAt A D T U (F.comp G) H M).hom ≫
      (perfectDGExtensionCompositionAt A D U V ((F.comp G).comp H) I M).hom ≫
      (perfectDGExtensionInputIso A D V
        (strictDGFunctor_comp_assoc (F.comp G) H I) M).hom ≫
      (perfectDGExtensionInputIso A D V
        (strictDGFunctor_comp_assoc F G (H.comp I)) M).hom =
    (perfectDGExtensionCompositionAt A T U V H I
        ((perfectDGExtension A E T G).obj ((perfectDGExtension A D E F).obj M))).hom ≫
      (perfectDGExtensionCompositionAt A E T V G (H.comp I)
        ((perfectDGExtension A D E F).obj M)).hom ≫
      (perfectDGExtensionCompositionAt A D E V F (G.comp (H.comp I)) M).hom := by
  have : (perfectDGModuleInclusion A V Set.univ).onClosed.Faithful := by
    dsimp only [perfectDGModuleInclusion]
    infer_instance
  apply (perfectDGModuleInclusion A V Set.univ).onClosed.map_injective
  simp only [CategoryTheory.Functor.map_comp, perfectDGExtension_closed_map_inclusion,
    perfectDGExtensionCompositionAt_inclusion, perfectDGExtensionInputIso_inclusion]
  exact dgModuleExtensionCompositionAt_fourfold A D E T U V F G H I M.val

end SerrePositivity.KST.SConstruction

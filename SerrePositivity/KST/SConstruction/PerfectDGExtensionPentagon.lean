module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionPentagon
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionFourfold

/-! # 実 Perf 延長の四重比較
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
  (H : DGFunctor A T U) (I : DGFunctor A U V) (M : PerfectDGModule A D)

/-- 元の実 Perf 四重比較の長経路も、入力等号移送を保って右結合を回収する。 -/
lemma perfectDGExtensionCompositionAt_fourfold_long :
    (perfectDGExtension A U V I).onClosed.map
        ((perfectDGExtension A T U H).onClosed.map
          (perfectDGExtensionCompositionAt A D E T F G M).hom) ≫
      (perfectDGExtension A U V I).onClosed.map
        (perfectDGExtensionCompositionAt A D T U (F.comp G) H M).hom ≫
      (perfectDGExtensionCompositionAt A D U V ((F.comp G).comp H) I M).hom ≫
      (perfectDGExtensionInputIso A D V
        (F := ((F.comp G).comp H).comp I) (G := (F.comp (G.comp H)).comp I)
        (congrArg (fun K => K.comp I) (strictDGFunctor_comp_assoc F G H)) M).hom ≫
      (perfectDGExtensionInputIso A D V
        (strictDGFunctor_comp_assoc F (G.comp H) I) M).hom ≫
      (perfectDGExtensionInputIso A D V
        (F := F.comp ((G.comp H).comp I)) (G := F.comp (G.comp (H.comp I)))
        (congrArg (fun K => F.comp K) (strictDGFunctor_comp_assoc G H I)) M).hom =
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
  exact dgModuleExtensionCompositionAt_fourfold_long A D E T U V F G H I M.val

/-- 元の実 Perf 四重比較の五角は、入力等号移送を保って可換。 -/
lemma perfectDGExtensionCompositionAt_pentagon :
    (perfectDGExtension A U V I).onClosed.map
        ((perfectDGExtension A T U H).onClosed.map
          (perfectDGExtensionCompositionAt A D E T F G M).hom) ≫
      (perfectDGExtension A U V I).onClosed.map
        (perfectDGExtensionCompositionAt A D T U (F.comp G) H M).hom ≫
      (perfectDGExtensionCompositionAt A D U V ((F.comp G).comp H) I M).hom ≫
      (perfectDGExtensionInputIso A D V
        (F := ((F.comp G).comp H).comp I) (G := (F.comp (G.comp H)).comp I)
        (congrArg (fun K => K.comp I) (strictDGFunctor_comp_assoc F G H)) M).hom ≫
      (perfectDGExtensionInputIso A D V
        (strictDGFunctor_comp_assoc F (G.comp H) I) M).hom ≫
      (perfectDGExtensionInputIso A D V
        (F := F.comp ((G.comp H).comp I)) (G := F.comp (G.comp (H.comp I)))
        (congrArg (fun K => F.comp K) (strictDGFunctor_comp_assoc G H I)) M).hom =
    (perfectDGExtension A U V I).onClosed.map
        ((perfectDGExtension A T U H).onClosed.map
          (perfectDGExtensionCompositionAt A D E T F G M).hom) ≫
      (perfectDGExtension A U V I).onClosed.map
        (perfectDGExtensionCompositionAt A D T U (F.comp G) H M).hom ≫
      (perfectDGExtensionCompositionAt A D U V ((F.comp G).comp H) I M).hom ≫
      (perfectDGExtensionInputIso A D V
        (strictDGFunctor_comp_assoc (F.comp G) H I) M).hom ≫
      (perfectDGExtensionInputIso A D V
        (strictDGFunctor_comp_assoc F G (H.comp I)) M).hom := by
  have : (perfectDGModuleInclusion A V Set.univ).onClosed.Faithful := by
    dsimp only [perfectDGModuleInclusion]
    infer_instance
  apply (perfectDGModuleInclusion A V Set.univ).onClosed.map_injective
  simp only [CategoryTheory.Functor.map_comp, perfectDGExtension_closed_map_inclusion,
    perfectDGExtensionCompositionAt_inclusion, perfectDGExtensionInputIso_inclusion]
  exact dgModuleExtensionCompositionAt_pentagon A D E T U V F G H I M.val

end SerrePositivity.KST.SConstruction

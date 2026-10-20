module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionComposition
public import SerrePositivity.KST.SConstruction.DGModuleExtensionTriangleEvaluation

/-! # 元の実 Perf 延長の単位三角
概要：既存の Perf 恒等・合成比較が、入力等号移送を含む元の三角を満たすと示す。
方針：全加群への包含の忠実性と、同じ実延長の閉零射作用の回収を使う。
規約：比較射を置き換えず元の同型を保持する。使われ方：関手的 Perf 模型の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の dg 入力の等号による、同じ実 Perf 延長の対象別同型。 -/
def perfectDGExtensionInputIso {F G : DGFunctor A D E} (h : F = G)
    (M : PerfectDGModule A D) :
    ForgetEnrichment.of (Complex A) ((perfectDGExtension A D E F).obj M) ≅
      ForgetEnrichment.of (Complex A) ((perfectDGExtension A D E G).obj M) :=
  eqToIso (congrArg (fun H => ForgetEnrichment.of (Complex A)
    ((perfectDGExtension A D E H).obj M)) h)

/-- 包含後の入力等号移送は、同じ元の実加群延長の入力移送。 -/
lemma perfectDGExtensionInputIso_inclusion {F G : DGFunctor A D E} (h : F = G)
    (M : PerfectDGModule A D) :
    (perfectDGModuleInclusion A E Set.univ).onClosed.map
        (perfectDGExtensionInputIso A D E h M).hom =
      (dgModuleExtensionInputIso A D E h M.val).hom := by
  cases h
  simp only [perfectDGExtensionInputIso, dgModuleExtensionInputIso,
    eqToIso_refl, Iso.refl_hom]
  exact (perfectDGModuleInclusion A E Set.univ).onClosed.map_id _

/-- 実 Perf 延長の閉零射作用は、包含後に同じ元の実延長の作用を回収する。 -/
lemma perfectDGExtension_closed_map_inclusion (F : DGFunctor A D E)
    {M N : ClosedCategory A (PerfectDGModule A D)} (f : M ⟶ N) :
    (perfectDGModuleInclusion A E Set.univ).onClosed.map
        ((perfectDGExtension A D E F).onClosed.map f) =
      (dgModuleExtension A D E F).onClosed.map
        ((perfectDGModuleInclusion A D Set.univ).onClosed.map f) := by
  change (ForgetEnrichment.homTo (Complex A) f ≫ (dgModuleExtension A D E F).map
      (ForgetEnrichment.to (Complex A) M).val (ForgetEnrichment.to (Complex A) N).val) ≫
      𝟙 (moduleHom A E
        ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) M).val)
        ((dgModuleExtension A D E F).obj (ForgetEnrichment.to (Complex A) N).val)) =
    (ForgetEnrichment.homTo (Complex A) f ≫ 𝟙 _) ≫ (dgModuleExtension A D E F).map _ _
  simp only [Category.comp_id]
  exact Category.comp_id _

/-- 元の実 Perf 恒等・合成比較の、入力等号移送を保つ単位三角。 -/
lemma perfectDGExtensionCompositionAt_id (F : DGFunctor A D E) (M : PerfectDGModule A D) :
    (perfectDGExtensionCompositionAt A D D E (DGFunctor.id D) F M).hom ≫
        (perfectDGExtensionInputIso A D E (strictDGFunctor_id_comp F) M).hom =
      (perfectDGExtension A D E F).onClosed.map (perfectDGExtensionIdentityAt A D M).hom := by
  have : (perfectDGModuleInclusion A E Set.univ).onClosed.Faithful := by
    dsimp only [perfectDGModuleInclusion]
    infer_instance
  apply (perfectDGModuleInclusion A E Set.univ).onClosed.map_injective
  rw [Functor.map_comp, perfectDGExtensionCompositionAt_inclusion,
    perfectDGExtensionInputIso_inclusion, perfectDGExtension_closed_map_inclusion,
    perfectDGExtensionIdentityAt_inclusion]
  exact dgModuleExtensionCompositionAt_id A D E F M.val

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionTriangle
public import SerrePositivity.KST.SConstruction.DGModuleExtensionTripleEvaluation

/-! # 元の実 Perf 延長の三重合成比較
概要：元の三重 Perf 比較の二経路が入力結合等号の移送を保って一致する。
方針：忠実な全加群への包含で、元の実加群延長の三重比較を回収する。
規約：元の対象・射・等号移送を保つ。使われ方：関手的な小さい Perf 模型の coherence。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z q
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z) (U : Type q)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T] [DGCategory A U] [Small.{u} U]
  (F : DGFunctor A D E) (G : DGFunctor A E T) (H : DGFunctor A T U)

/-- 同じ元の三重 Perf 比較の二経路は、結合の入力等号の移送を保って一致する。 -/
lemma perfectDGExtensionCompositionAt_assoc (M : PerfectDGModule A D) :
    (perfectDGExtension A T U H).onClosed.map
        (perfectDGExtensionCompositionAt A D E T F G M).hom ≫
      (perfectDGExtensionCompositionAt A D T U (F.comp G) H M).hom ≫
      (perfectDGExtensionInputIso A D U (strictDGFunctor_comp_assoc F G H) M).hom =
    (perfectDGExtensionCompositionAt A E T U G H ((perfectDGExtension A D E F).obj M)).hom ≫
      (perfectDGExtensionCompositionAt A D E U F (G.comp H) M).hom := by
  have : (perfectDGModuleInclusion A U Set.univ).onClosed.Faithful := by
    dsimp only [perfectDGModuleInclusion]
    infer_instance
  apply (perfectDGModuleInclusion A U Set.univ).onClosed.map_injective
  simp only [CategoryTheory.Functor.map_comp, perfectDGExtension_closed_map_inclusion,
    perfectDGExtensionCompositionAt_inclusion, perfectDGExtensionInputIso_inclusion]
  exact dgModuleExtensionCompositionAt_assoc A D E T U F G H M.val

end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputHomHorizontal
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionParameterComposition
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionInputHom

/-! # 元の実 Perf 延長と入力 Hom end の横合成
概要：元の二つの入力 Hom end の作用は、実 Perf の合成比較と全次数で両立する。
方針：実加群の横合成則を、同じ全 Hom と比較を持つ充満 dg 部分圏へ制限する。
規約：元の実 Perf と比較を保持する。使われ方：ラベル付き模型への厳密な移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 元の入力横合成は、同じ実 Perf の合成比較の共役によって厳密に回収される。 -/
lemma perfectDGExtensionInputHom_horizontal (F F' : DGFunctor A D E)
    (G G' : DGFunctor A E T) (M : PerfectDGModule A D) :
    ((perfectDGExtensionInputHom A D E F F' M ≫ (perfectDGExtension A E T G).map
          ((perfectDGExtension A D E F).obj M) ((perfectDGExtension A D E F').obj M)) ⊗ₘ
        perfectDGExtensionInputHom A E T G G' ((perfectDGExtension A D E F').obj M)) ≫
        eComp (Complex A)
          ((perfectDGExtension A E T G).obj ((perfectDGExtension A D E F).obj M))
          ((perfectDGExtension A E T G).obj ((perfectDGExtension A D E F').obj M))
          ((perfectDGExtension A E T G').obj ((perfectDGExtension A D E F').obj M)) ≫
          enrichedClosedIsoConjugation (Complex A) (perfectDGExtensionCompositionAt A D E T F G M)
            (perfectDGExtensionCompositionAt A D E T F' G' M) =
      dgFunctorHorizontal A D E T F F' G G' ≫
        perfectDGExtensionInputHom A D T (F.comp G) (F'.comp G') M :=
  dgModuleExtensionInputHom_horizontal A D E T F F' G G' M.val

end SerrePositivity.KST.SConstruction

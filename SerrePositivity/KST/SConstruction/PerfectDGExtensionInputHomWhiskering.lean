module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputHomWhiskering
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionParameterComposition
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionInputHom
public import SerrePositivity.KST.SConstruction.DGParameterClosedNaturality

/-! # 実 Perf 入力 Hom の前後合成と同型自然性
概要：元の実 Perf 入力 Hom 作用は、入力の前後合成と対象の実閉零同型を保持する。
方針：元の実加群の式を制限し、全パラメータ自然性から同型の共役を得る。
規約：元の Hom end・実比較を保つ。使われ方：ラベル付き入力 Hom への移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 元の入力 Hom の後合成は、実 Perf の同じ合成比較の共役で回収される。 -/
lemma perfectDGExtensionInputHom_post {F F' : DGFunctor A D E} (G : DGFunctor A E T)
    (M : PerfectDGModule A D) :
    (perfectDGExtensionInputHom A D E F F' M ≫ (perfectDGExtension A E T G).map
        ((perfectDGExtension A D E F).obj M) ((perfectDGExtension A D E F').obj M)) ≫
        enrichedClosedIsoConjugation (Complex A) (perfectDGExtensionCompositionAt A D E T F G M)
          (perfectDGExtensionCompositionAt A D E T F' G M) =
      dgFunctorHomPost A D E T G F F' ≫
        perfectDGExtensionInputHom A D T (F.comp G) (F'.comp G) M :=
  dgModuleExtensionInputHom_post A D E T G M.val

/-- 元の入力 Hom の前合成は、実 Perf の同じ合成比較の共役で回収される。 -/
lemma perfectDGExtensionInputHom_pre {G G' : DGFunctor A E T} (F : DGFunctor A D E)
    (M : PerfectDGModule A D) :
    perfectDGExtensionInputHom A E T G G' ((perfectDGExtension A D E F).obj M) ≫
        enrichedClosedIsoConjugation (Complex A) (perfectDGExtensionCompositionAt A D E T F G M)
          (perfectDGExtensionCompositionAt A D E T F G' M) =
      dgFunctorHomPre A E T D F G G' ≫
        perfectDGExtensionInputHom A D T (F.comp G) (F.comp G') M :=
  dgModuleExtensionInputHom_pre A D E T F M.val

omit [DGCategory A D] [Small.{u} D] in
/-- 元の実 Perf 入力 Hom の作用は、入力対象の同じ実閉零同型の像による共役と可換。 -/
lemma perfectDGExtensionInputHom_conjugation (G G' : DGFunctor A E T)
    {M N : PerfectDGModule A E}
    (e : ForgetEnrichment.of (Complex A) M ≅ ForgetEnrichment.of (Complex A) N) :
    perfectDGExtensionInputHom A E T G G' M ≫ enrichedClosedIsoConjugation (Complex A)
        ((perfectDGExtension A E T G).onClosed.mapIso e)
        ((perfectDGExtension A E T G').onClosed.mapIso e) =
      perfectDGExtensionInputHom A E T G G' N :=
  dgFunctorParameter_conjugation A
    (perfectDGExtensionParameter A E T
      (dgFunctorHomEquiv A E T (dgFunctorHom A E T G G') G G' (𝟙 _))) e

end SerrePositivity.KST.SConstruction

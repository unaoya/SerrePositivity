module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionParameterComposition
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionComposition
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionParameter

/-! # 元の実 Perf 延長の合成比較の全入力自然性
概要：任意 K の入力作用は、元の実 Perf の合成比較による共役と両立する。
方針：元の実加群の式を、同じ Hom を持つ充満 dg 部分圏へ制限する。
規約：元の合成比較を保ち、Perf 全体の end は作らない。使われ方：ラベル付き入力横合成。
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

/-- 左入力の全次数作用は、元の実 Perf 合成比較の共役後に後合成を回収する。 -/
lemma perfectDGExtensionComposition_parameter_post {K : Complex A}
    {F F' : DGFunctor A D E} (G : DGFunctor A E T)
    (τ : DGFunctorParamTrans A D E K F F') (M : PerfectDGModule A D) :
    ((perfectDGExtensionParameter A D E τ).app M ≫ (perfectDGExtension A E T G).map
        ((perfectDGExtension A D E F).obj M) ((perfectDGExtension A D E F').obj M)) ≫
        enrichedClosedIsoConjugation (Complex A) (perfectDGExtensionCompositionAt A D E T F G M)
          (perfectDGExtensionCompositionAt A D E T F' G M) =
      (perfectDGExtensionParameter A D T (dgFunctorParamPost A D E T G τ)).app M :=
  dgModuleExtensionComposition_parameter_post A D E T G τ M.val

/-- 右入力の全次数作用は、元の実 Perf 合成比較の共役後に前合成を回収する。 -/
lemma perfectDGExtensionComposition_parameter_pre {K : Complex A}
    {G G' : DGFunctor A E T} (F : DGFunctor A D E)
    (τ : DGFunctorParamTrans A E T K G G') (M : PerfectDGModule A D) :
    (perfectDGExtensionParameter A E T τ).app ((perfectDGExtension A D E F).obj M) ≫
        enrichedClosedIsoConjugation (Complex A) (perfectDGExtensionCompositionAt A D E T F G M)
          (perfectDGExtensionCompositionAt A D E T F G' M) =
      (perfectDGExtensionParameter A D T (dgFunctorParamPre A E T D F τ)).app M :=
  dgModuleExtensionComposition_parameter_pre A D E T F τ M.val

end SerrePositivity.KST.SConstruction

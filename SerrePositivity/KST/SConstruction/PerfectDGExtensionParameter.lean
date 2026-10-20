module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionParameter
public import SerrePositivity.KST.SConstruction.PerfectDGExtension

/-! # 全パラメータの元の実 Perf 延長への作用
概要：K パラメータを変更せず、元の実加群延長の自然変換を実 Perf へ制限する。
方針：Perf の充満 dg 構造が保持する同じ全 Hom 複体を使う。
規約：Perf の対象型の smallness を要求しない。使われ方：ラベル付き Perf の高次作用。
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

/-- 元の実 Perf 延長間の、同じ K を保持する全次数自然変換。 -/
def perfectDGExtensionParameter {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) :
    DGFunctorParamTrans A (PerfectDGModule A D) (PerfectDGModule A E) K
      (perfectDGExtension A D E F) (perfectDGExtension A D E G) where
  app M := (dgModuleExtensionParameter A D E τ).app M.val
  naturality M N := (dgModuleExtensionParameter A D E τ).naturality M.val N.val

/-- 元の Perf 対象での全 Hom 成分は、同じ実加群作用を回収する。 -/
lemma perfectDGExtensionParameter_app {K : Complex A} {F G : DGFunctor A D E}
    (τ : DGFunctorParamTrans A D E K F G) (M : PerfectDGModule A D) :
    (perfectDGExtensionParameter A D E τ).app M =
      (dgModuleExtensionParameter A D E τ).app M.val := rfl

end SerrePositivity.KST.SConstruction

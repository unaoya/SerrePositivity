module
public import SerrePositivity.KST.SConstruction.DGModuleExtensionInputHomComposition
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionParameter

/-! # 元の入力 Hom の実 Perf 延長への作用
概要：元の実加群延長の入力 Hom 作用を、同じ全 Hom を持つ実 Perf に制限する。
方針：元の普遍パラメータ成分と、既存の実加群の単位・合成保存を保持する。
規約：Perf 全体の end を作らない。使われ方：ラベル付き入力 Hom の合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の入力 Hom から、各実 Perf 延長間の全 Hom への chain map。 -/
def perfectDGExtensionInputHom (F G : DGFunctor A D E) (M : PerfectDGModule A D) :
    dgFunctorHom A D E F G ⟶ homObject A (PerfectDGModule A E)
      ((perfectDGExtension A D E F).obj M) ((perfectDGExtension A D E G).obj M) :=
  (perfectDGExtensionParameter A D E
    (dgFunctorHomEquiv A D E (dgFunctorHom A D E F G) F G (𝟙 _))).app M

/-- 実 Perf の入力 Hom 作用は、元の同じ実加群の入力 Hom 作用。 -/
lemma perfectDGExtensionInputHom_module (F G : DGFunctor A D E) (M : PerfectDGModule A D) :
    perfectDGExtensionInputHom A D E F G M = dgModuleExtensionInputHom A D E F G M.val :=
  perfectDGExtensionParameter_app A D E
    (dgFunctorHomEquiv A D E (dgFunctorHom A D E F G) F G (𝟙 _)) M

/-- 元の入力 Hom の全次数合成は、同じ実 Perf 延長の全 Hom 合成へ送られる。 -/
lemma perfectDGExtensionInputHom_composition (F G H : DGFunctor A D E)
    (M : PerfectDGModule A D) :
    dgFunctorComposition A D E F G H ≫ perfectDGExtensionInputHom A D E F H M =
      (perfectDGExtensionInputHom A D E F G M ⊗ₘ perfectDGExtensionInputHom A D E G H M) ≫
        eComp (Complex A) ((perfectDGExtension A D E F).obj M)
          ((perfectDGExtension A D E G).obj M) ((perfectDGExtension A D E H).obj M) :=
  dgModuleExtensionInputHom_composition A D E F G H M.val

end SerrePositivity.KST.SConstruction

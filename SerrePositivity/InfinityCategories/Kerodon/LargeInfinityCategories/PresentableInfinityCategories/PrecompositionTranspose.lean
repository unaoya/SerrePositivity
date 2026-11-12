module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrecompositionHom
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FunctorCompositionEvaluation
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionHomotopy

/-!
概要：前合成作用のパラメータ族を転置し、元の Hom の後合成に一致させる。
方針：豊穣前合成の評価を全単体の内部 Hom の成分で計算する。
規約：充填性を要求せず、単体集合の射としての厳密な等式を扱う。
使われ方：対応空間の単位の族と前合成の Hom 全単射を接続する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：前合成作用を任意の関手族で評価して転置すると、転置した族による後合成。
方針：二重内部 Hom の各成分を展開し、元の族の自然性で比較する。
規約：族のパラメータと標的を任意の単体集合とする。
使われ方：元の単位を全パラメータの前合成の単位へ移す。 -/
lemma precompositionMap_transpose_evaluate {A C Z : SSet.{u}}
    (U : A ⟶ (ihom C).obj Z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorPrecompositionMap C C Z ≫ (pre U).app ((ihom C).obj Z) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A C Z).hom =
      (ihom C).map (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorTranspose U) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro c
  apply CategoryTheory.Functor.functorHom_ext
  intro e β
  apply ConcreteCategory.hom_ext
  intro a
  change (U.app e a).app e (𝟙 e)
      (f.app e ((α ≫ β) ≫ 𝟙 e) (C.map β c)) =
    (U.app e a).app e (𝟙 e) (C.map β (f.app d α c))
  rw [Category.comp_id]
  exact congrArg (fun z ↦ (U.app e a).app e (𝟙 e) z)
    (ConcreteCategory.congr_hom (f.naturality β α) c)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

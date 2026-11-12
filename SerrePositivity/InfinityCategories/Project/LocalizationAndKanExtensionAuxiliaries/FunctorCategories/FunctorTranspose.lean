module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.InternalHomSwapNaturality

/-!
概要：関手単体集合に値を取る図式の二つの変数の転置。
方針：内部 Hom の交換同型を関手の頂点へ適用する。
規約：全ての単体集合を任意とする。
使われ方：境界の余錐の族と境界関手圏に値を取る余錐の厳密な対応。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：二変数の図式を転置して二つの始域を交換する。
方針：uncurry の二因子を対称性で交換して再び curry する。
規約：f のパラメータを値域の関手空間の始域へ移す。
使われ方：局所の境界固定の余錐条件の比較。 -/
def functorTranspose {A B D : SSet.{u}} (f : A ⟶ (ihom B).obj D) :
    B ⟶ (ihom A).obj D := curry ((β_ A B).hom ≫ uncurry f)

/-- 概要：図式の転置は内部 Hom の交換同型の頂点での作用。
方針：交換同型の関手頂点の計算則を使う。
規約：定義との厳密な一致。
使われ方：転置の自然性と二重転置の検証。 -/
lemma functorTranspose_vertex {A B D : SSet.{u}} (f : A ⟶ (ihom B).obj D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (functorTranspose f) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A B D).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) := rfl

/-- 概要：二度転置すると元の図式に戻る。
方針：関手頂点の単射性と内部 Hom の二度の交換が恒等であることを使う。
規約：ホモトピーではなく射の等式。
使われ方：境界の局所延長を元の指定図式に合わせる。 -/
lemma functorTranspose_transpose {A B D : SSet.{u}} (f : A ⟶ (ihom B).obj D) :
    functorTranspose (functorTranspose f) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  rw [functorTranspose_vertex, functorTranspose_vertex]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso A B D).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso B A D).hom).app
    (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_hom_hom]
  rfl

/-- 概要：転置は元のパラメータへの前合成を関手の制限へ移す。
方針：内部 Hom の交換と第一始域への前合成の自然性を頂点で読む。
規約：パラメータの射 i は任意。
使われ方：余錐の族の境界固定条件を相対余錐の像の条件へ移す。 -/
lemma functorTranspose_pre_left {A₀ A B D : SSet.{u}}
    (i : A₀ ⟶ A) (f : A ⟶ (ihom B).obj D) :
    functorTranspose (i ≫ f) = functorTranspose f ≫ (pre i).app D := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.internalHomSwap_pre_left i B D) (Opposite.op ⦋0⦌)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)

/-- 概要：転置は関手の始域への制限を転置後のパラメータへの前合成へ移す。
方針：両辺を再び転置し、第一パラメータへの前合成の自然性を使う。
規約：関手の始域の射 j は任意。
使われ方：余錐制限の固定図式の等式を転置する。 -/
lemma functorTranspose_pre_right {A B₀ B D : SSet.{u}}
    (j : B₀ ⟶ B) (f : A ⟶ (ihom B).obj D) :
    functorTranspose (f ≫ (pre j).app D) = j ≫ functorTranspose f := by
  have h := functorTranspose_pre_left j (functorTranspose f)
  rw [functorTranspose_transpose] at h
  have ht := congrArg functorTranspose h
  rw [functorTranspose_transpose] at ht
  exact ht.symm

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

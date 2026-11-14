module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.CochainModels.Cochains.CommonComplexUniverseComposition
/-!
概要：任意の追加共通宇宙でも、逆向きの標準変更は元の標準変更の逆射である。
方針：同じ全単体の同じ宇宙変更関数を比較する。
規約：共通宇宙と全パラメーターを保持する。
使われ方：元の Hom 複体模型同型の逆を任意対象宇宙の関手評価へ接続する。
-/
@[expose] public section
noncomputable section
universe u v w r
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] (K : Complex R)
lemma dgGluingCommonComplexUniverse_reverse :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,v,w,r} K).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCommonComplexPinchedUniverseIso.{u,w,v,r} K).inv := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

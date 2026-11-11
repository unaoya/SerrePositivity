module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorPinchedIso
public import SerrePositivity.EInfinity.ComplexLimits.ComplexPinchedPrecomposition

/-!
# 元の正規化 Hom 前合成が表す全区間族

概要：元の複体射による正規化 Hom の前合成は、同じ dg nerve の射の前合成を表す。
方針：同じ実 DK/pinched 同型の全作用と小ささなしの全族公式を使う。
規約：任意パラメータ K と元の複体射を保つ。
使われ方：実自由単位の前合成と ∞ 写像空間の標準作用の接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

lemma normalizedTensorPinchedIso_precomp_family {X X' : Complex A} (Y : Complex A)
    (f : X' ⟶ X) (K : SSet.{u + 1})
    (g : K ⟶ SSet.uliftFunctor.{u + 1, u}.obj
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X)).obj Y)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A)
      (g ≫ SSet.uliftFunctor.{u + 1, u}.map
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((normalizedSimplexTensorFamily A).map f)).app Y) ≫
          (normalizedTensorPinchedIso A X' Y).hom) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedEdge A (Complex A) ((complexToClosed A).map f))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedFamilyHom A (Complex A) (g ≫ (normalizedTensorPinchedIso A X Y).hom) := by
  rw [normalizedTensorPinchedIso_precomp]
  simpa only [Category.assoc] using complexPinchedPrecomposition_family A f Y K
    (g ≫ (normalizedTensorPinchedIso A X Y).hom)

end SerrePositivity.EInfinity.ComplexLimits

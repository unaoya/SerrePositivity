module

public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.DoldKanIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.InfinityCategory

/-!
# 実正規化単体テンソル Hom と既存 D(R) の写像空間

概要：元の半自由複体の正規化単体テンソル Hom を、同じ D(R) の右 pinched Hom へ同定する。
方針：全単体作用素と可換な実 Dold–Kan Hom 同型と既存 N4 の同型を合成する。
規約：既存 derivedInfinityCategory と元の半自由対象を保持する。
使われ方：元の標準 frame Hom と実 ∞ 写像空間の弱比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory
open SerrePositivity.DifferentialGraded
open SerrePositivity.HomotopyFunctionComplex SerrePositivity.InfinityCategories

open scoped Simplicial
variable (A : Type u) [CommRing A]

def normalizedSimplexDerivedHomIso (X Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) :
    SSet.uliftFunctor.{u + 1, u}.obj
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X.val)).obj Y.val) ≅
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom (X := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex Y) := by
  have e : (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (normalizedSimplexTensor A X.val)).obj Y.val ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomSpace (R := A) (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree A) X Y :=
    normalizedSimplexTensorHomIso A X.val Y.val
  exact SSet.uliftFunctor.{u + 1, u}.mapIso e ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanHomPinchedIso X Y

end SerrePositivity.EInfinity.ComplexLimits

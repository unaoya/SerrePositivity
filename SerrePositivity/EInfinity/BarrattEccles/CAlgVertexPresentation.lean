module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgQuasiIso
public import SerrePositivity.EInfinity.BarrattEccles.AlgebraRelativeComparisons
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.NerveWeakVertexIso

/-!
# 任意 CAlg_R 頂点の元の代数による表示

概要：元の coherent nerve の各頂点は、同じ cofibrant 代数の全代数頂点と同型。
方針：元の置換比較を同じ局所化源で反転する。
規約：元の頂点の実代数表示と指定比較射を保持する。
使われ方：離散対象の特徴付けの任意頂点への適用。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.InfinityCategories _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped Simplicial
variable (A : Type u) [CommRing A]

def cAlgLocalizationVertexIsoOfWeak
    {X Y : (cofibrantAlgebraRelativeCategory A).category} (f : X ⟶ Y)
    (hf : (cofibrantAlgebraRelativeCategory A).weakEquivalences f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (cAlgVertexEquiv A X) (cAlgVertexEquiv A Y) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexIsoOfWeak (cofibrantAlgebraRelativeCategory A) f hf

def cAlgVertexOfCofibrantIso (X : (cofibrantAlgebraRelativeCategory A).category) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (cAlgVertex A ((cofibrantAlgebraDKInclusion A).obj X))
      (cAlgVertexEquiv A X) :=
  cAlgLocalizationVertexIsoOfWeak A ((cofibrantDKComparison A).app X)
    (cofibrantDKComparison_weak A X)

def cAlgVertexRepresentative (x : (CAlg_R A) _⦋0⦌) : (operad A).Algebra :=
  (cofibrantAlgebraDKInclusion A).obj ((cAlgVertexEquiv A).symm x)

def cAlgVertexRepresentativeIso (x : (CAlg_R A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (cAlgVertex A (cAlgVertexRepresentative A x)) x :=
  cAlgVertexOfCofibrantIso A ((cAlgVertexEquiv A).symm x) ≪≫
    eqToIso (congrArg HomotopyCategory.mk ((cAlgVertexEquiv A).apply_symm_apply x))

end SerrePositivity.EInfinity.BarrattEccles

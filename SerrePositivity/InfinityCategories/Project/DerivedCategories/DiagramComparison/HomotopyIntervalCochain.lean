module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.NormalizedIntervalCycleData
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
/-!
概要：与えた鎖ホモトピーを、同じ正規化区間から内部Homへの写像へ送る。
方針：零次のf,gと負のホモトピーコチェインを区間の境界データへ入れる。
規約：A06の構成の分割。δh=f−gに対し辺は−hとする。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
/-- 同じホモトピーから得られる内部Homへの指定正規化区間の評価。 -/
def homotopyIntervalCochainMap (A : Type u) [CommRing A]
    {C : Type v} [Category.{u} C] [Preadditive C] [Linear A C]
    {R S : CochainComplex C ℤ} (f g : R ⟶ S) (h : Homotopy f g) :
    (SerrePositivity.EInfinity.BarrattEccles.normalizedFunctor A).obj
      (SSet.stdSimplex.obj ⦋1⦌) ⟶ linearHomComplex A R S := by
  refine normalizedIntervalCochainMapOfBoundary A (linearHomComplex A R S)
    (Cochain.ofHom f) (Cochain.ofHom g) ?_ ?_ (-Cochain.ofHomotopy h) ?_
  · change δ 0 1 (Cochain.ofHom f) = 0
    exact δ_ofHom f
  · change δ 0 1 (Cochain.ofHom g) = 0
    exact δ_ofHom g
  · rw [map_neg]
    change -δ (-1) 0 (Cochain.ofHomotopy h) = Cochain.ofHom g - Cochain.ofHom f
    rw [δ_ofHomotopy, neg_sub]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

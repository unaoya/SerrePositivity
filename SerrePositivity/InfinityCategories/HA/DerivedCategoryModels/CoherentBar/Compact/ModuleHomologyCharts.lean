module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.HomologyChartsPiData
/-!
概要：単体的加群の実余錐に、全基点ホモロジーチャートと五条件を与える。
方針：同じ図式と脚を Moore 正規化・ホモロジーへ送り、自然性を使う。
規約：各次数のホモロジー余極限性だけを入力とし、空間の余極限性を仮定しない。
使われ方：評価複体の線形模型を native 評価空間へ比較する前の接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory Limits AlgebraicTopology SSet
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {I : Type u} [PartialOrder I]
  (W : I ⥤ SimplicialObject (ModuleCat.{u} R)) (c : Cocone W)
  [∀ i, KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (W.obj i))]
  [KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet c.pt)]

/-- 元の実脚を保持した、各次数の正規化 Moore ホモロジー関手。 -/
def dgBarCompactModuleHomologyFunctor (n : ℕ) :
    SimplicialObject (ModuleCat.{u} R) ⥤ ModuleCat.{u} R :=
  normalizedMooreComplex (ModuleCat.{u} R) ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- Moore ホモロジー余極限性を、同じ単体的加群の全基点チャートへ渡す。 -/
def dgBarCompactModuleHomologyCharts
    (hc : ∀ n, IsColimit ((dgBarCompactModuleHomologyFunctor (R := R) n).mapCocone c)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactHomologyCharts R
      (fun i => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (W.obj i), inferInstance⟩)
      ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet c.pt, inferInstance⟩
      (fun {_ _} h => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (W.map (homOfLE h)))
      (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (c.ι.app i)) where
  diagram n := W ⋙ dgBarCompactModuleHomologyFunctor n
  cocone n := (dgBarCompactModuleHomologyFunctor n).mapCocone c
  isColimit := hc
  zeroStage i := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroMooreEquiv (W.obj i)
  zeroApex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroMooreEquiv c.pt
  zero_leg i y := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroMooreEquiv_naturality (c.ι.app i) (π₀.mk y)
  zero_transition := by
    intro i j h y
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.modulePiZeroMooreEquiv_naturality (W.map (homOfLE h)) (π₀.mk y)
  positiveStage n i y := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv (W.obj i) n y).toEquiv
  positiveApex n z := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv c.pt n z).toEquiv
  positive_leg n i y a := by
    have : KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (((Functor.const I).obj c.pt).obj i)) :=
      inferInstanceAs (KanComplex (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet c.pt))
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv_naturality (c.ι.app i) n y a
  positive_transition := by
    intro n i j h y a
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiHomologyEquiv_naturality (W.map (homOfLE h)) n y a
  transport := by
    intro n x y e a b he
    exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactModulePiTransport_of_homology_eq n e a b he

/-- 実加群余錐の全次数ホモロジー余極限性は、橋の五条件を与える。 -/
lemma dgBarCompactModulePiData_of_homologyColimit [IsFiltered I]
    (hc : ∀ n, IsColimit ((dgBarCompactModuleHomologyFunctor (R := R) n).mapCocone c)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.DGBarCompactSpacePiData
      (fun i => ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet (W.obj i), inferInstance⟩)
      ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSet c.pt, inferInstance⟩
      (fun {_ _} h => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (W.map (homOfLE h)))
      (fun i => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleUnderlyingSSetMap (c.ι.app i)) :=
  _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactPiData_of_homologyCharts (dgBarCompactModuleHomologyCharts W c hc)

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact

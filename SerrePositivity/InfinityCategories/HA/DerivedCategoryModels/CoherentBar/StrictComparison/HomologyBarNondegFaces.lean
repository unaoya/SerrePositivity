module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarSplitting
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

/-!
概要：poset 上の非退化ホモロジー bar の面射を係数ごとに構成する。
方針：strict な頂点列の各面も非退化であることを使う。
規約：零番の面は F の辺の射を保持する。
使われ方：coherent bar の一次ホモロジー微分との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits Opposite SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] {J : Type u} [PartialOrder J]
  (F : J ⥤ ModuleCat.{u} R)

def dgHomologyBarNondegFace {n : ℕ} (s : (nerve J).nonDegenerate (n + 1))
    (i : Fin (n + 2)) : (nerve J).nonDegenerate n :=
  ⟨(nerve J).δ i s.val, (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono _).mpr (by
    intro a b hab
    rw [nerve.δ_obj, nerve.δ_obj]
    exact ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.val).mp s.property)
      (Fin.strictMono_succAbove i hab))⟩

def dgHomologyBarNondegFaceMap (n : ℕ) (i : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegGraded R F (n + 1) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegGraded R F n :=
  Sigma.desc (fun s => F.map (s.val.map (homOfLE (Fin.zero_le (i.succAbove 0)))) ≫
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegFamily R F n) (dgHomologyBarNondegFace s i))

@[reassoc (attr := simp)]
lemma dgHomologyBarNondegFaceMap_ι (n : ℕ) (i : Fin (n + 2))
    (s : (nerve J).nonDegenerate (n + 1)) :
    Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegFamily R F (n + 1)) s ≫ dgHomologyBarNondegFaceMap R F n i =
    F.map (s.val.map (homOfLE (Fin.zero_le (i.succAbove 0)))) ≫
      Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegFamily R F n) (dgHomologyBarNondegFace s i) := by
  simp only [dgHomologyBarNondegFaceMap, Sigma.ι_comp_desc]

@[reassoc]
lemma dgHomologyBarNondegFaceMap_inclusion (n : ℕ) (i : Fin (n + 2)) :
    dgHomologyBarNondegFaceMap R F n i ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegInclusion R F n =
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegInclusion R F (n + 1) ≫ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F).δ i := by
  apply Sigma.hom_ext
  intro s
  simp only [dgHomologyBarNondegFaceMap_ι_assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegInclusion_ι_assoc,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegInclusion_ι, SimplicialObject.δ,
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarMap_ι]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.HomologyBarSplittingIndex

/-!
概要：bar の非退化ラベル直和と、全射に沿う係数同型を作る。
方針：全射が始点を保つことから、bar の実係数射を同型にする。
規約：同じホモロジー係数 F を保つ。
使われ方：通常の bar の canonical splitting。
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

abbrev dgHomologyBarNondegFamily (n : ℕ) (s : (nerve J).nonDegenerate n) : ModuleCat R :=
  F.obj (s.val.obj 0)

abbrev dgHomologyBarNondegGraded (n : ℕ) : ModuleCat R :=
  ∐ dgHomologyBarNondegFamily R F n

def dgHomologyBarNondegInclusion (n : ℕ) :
    dgHomologyBarNondegGraded R F n ⟶ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F) _⦋n⦌ :=
  Sigma.desc (fun s => Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F (op ⦋n⦌)) s.val)

@[reassoc (attr := simp)]
lemma dgHomologyBarNondegInclusion_ι (n : ℕ) (s : (nerve J).nonDegenerate n) :
    Sigma.ι (dgHomologyBarNondegFamily R F n) s ≫ dgHomologyBarNondegInclusion R F n =
      Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F (op ⦋n⦌)) s.val := by
  simp only [dgHomologyBarNondegInclusion, Sigma.ι_comp_desc]

def dgHomologyBarSplittingCoefficientIso (Δ : SimplexCategoryᵒᵖ)
    (A : SimplicialObject.Splitting.IndexSet Δ)
    (s : (nerve J).nonDegenerate A.1.unop.len) :
    dgHomologyBarNondegFamily R F A.1.unop.len s ≅
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F Δ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplittingIndexEquiv (J := J) Δ ⟨A, s⟩) := by
  let f := s.val.map (homOfLE (Fin.zero_le (A.e.toOrderHom 0)))
  have hobj : s.val.obj 0 = s.val.obj (A.e.toOrderHom 0) := by
    rw [_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplitting_epi_zero]
  have hf : f = eqToHom hobj := Subsingleton.elim _ _
  letI : IsIso f := by rw [hf]; infer_instance
  exact asIso (F.map f)

lemma dgHomologyBarSplittingCoefficientIso_hom (Δ : SimplexCategoryᵒᵖ)
    (A : SimplicialObject.Splitting.IndexSet Δ)
    (s : (nerve J).nonDegenerate A.1.unop.len) :
    (dgHomologyBarSplittingCoefficientIso R F Δ A s).hom =
      F.map (s.val.map (homOfLE (Fin.zero_le (A.e.toOrderHom 0)))) := rfl

lemma dgHomologyBarSplitting_leg (Δ : SimplexCategoryᵒᵖ)
    (A : SimplicialObject.Splitting.IndexSet Δ) :
    dgHomologyBarNondegInclusion R F A.1.unop.len ≫ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSimplicial R F).map A.e.op =
    Sigma.desc (fun s => (dgHomologyBarSplittingCoefficientIso R F Δ A s).hom ≫
      Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarFamily R F Δ) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarSplittingIndexEquiv (J := J) Δ ⟨A, s⟩)) := by
  apply Sigma.hom_ext
  intro s
  erw [← Category.assoc, dgHomologyBarNondegInclusion_ι, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarMap_ι, Sigma.ι_comp_desc]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

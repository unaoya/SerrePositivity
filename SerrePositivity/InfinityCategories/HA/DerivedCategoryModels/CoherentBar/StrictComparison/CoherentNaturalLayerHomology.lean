module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentLayerHomologyInclusions
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.CoherentPrefixHomologyDiagram

/-!
概要：総次数を指定した実次元層ホモロジーと非退化 H(G) 係数直和の同型。
方針：各始点の実等号射を使う自然なホモロジー同型で係数を再添字付けする。
規約：全整数次数を扱い、次元と次数の和を明示する。
使われ方：一次複体の面和を同じ総次数の通常の bar へ比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
open CategoryTheory Limits DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {J : Type u} [PartialOrder J]
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj (nerve J) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R D))

def dgCoherentBarNaturalLayerHomologyIso (x : D) (n : ℕ) (q r : ℤ) (h : (n : ℤ) + q = r) :
    ((moduleEvaluation R D x).obj (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerGraded R D G n)).homology q ≅
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegGraded R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r) n := by
  subst r
  let V := fun t : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndex (nerve J) n =>
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G t.val.val).obj (Opposite.op x)).homology ((n : ℤ) + q)
  exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerHomologyIso R D G x q n ≪≫
    (Sigma.reindex (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndexEquiv (nerve J) n) V).symm ≪≫
      Sigma.mapIso (fun s => by
        change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n, s.val⟩).obj
          (Opposite.op x)).homology ((n : ℤ) + q) ≅ _
        exact _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso R D G x ((n : ℤ) + q) n s.val)

@[reassoc]
lemma dgCoherentBarNaturalLayerHomologyIso_ι (x : D) (n : ℕ) (q r : ℤ)
    (h : (n : ℤ) + q = r) (s : (nerve J).nonDegenerate n) :
    HomologicalComplex.homologyMap ((_root_.SerrePositivity.DifferentialGraded.moduleEvaluation R D x).map
      (Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerFamily R D G n)
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndexEquiv (nerve J) n s))) q ≫
      (dgCoherentBarNaturalLayerHomologyIso R D G x n q r h).hom =
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgComplexShiftHomologyIso R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G ⟨n, s.val⟩).obj (Opposite.op x))
      (n : ℤ) q r h).hom ≫ (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarSourceHomologyIso R D G x r n s.val).hom ≫
        Sigma.ι (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgHomologyBarNondegFamily R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarHomologyDiagram R D G x r) n) s := by
  subst r
  let e := _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndexEquiv (nerve J) n
  let V := fun t : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerIndex (nerve J) n =>
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentBarSource R D G t.val.val).obj (Opposite.op x)).homology ((n : ℤ) + q)
  have hi : Sigma.ι V (e s) ≫ (Sigma.reindex e V).inv = Sigma.ι (V ∘ e) s := by
    rw [← Sigma.ι_reindex_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [dgCoherentBarNaturalLayerHomologyIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgCoherentBarLayerHomologyIso_ι, Category.assoc,
    Category.assoc, ← Category.assoc (Sigma.ι V (e s)) (Sigma.reindex e V).inv]
  erw [hi]
  rw [Sigma.ι_mapIso_hom]
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

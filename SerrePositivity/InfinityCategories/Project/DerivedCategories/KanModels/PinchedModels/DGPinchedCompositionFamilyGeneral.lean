module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGPinchedCompositionFamilyPrism
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.FunctorComparisons.DGCoherentCompositionNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.PinchedModels.DGStandardPinchedNaturality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceOverEqualityTransport
/-!
概要：元の coherent 合成 prism の両入力に対する dg 関手自然性を公開する。
方針：標準 DK 係数と coherent 比較の自然性を、固定標的の slice へ移す。
規約：Small 仮定なしに全パラメーター・全時刻・端点輸送を保持する。
使われ方：D2 の閉前合成・閉後合成 prism を同じ coherent 構成のまま比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open SSet
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]

lemma dgPinchedCompositionTargetPoint_naturality (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (z : D) :
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Q.obj z)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_hom_heq _ _

lemma dgPinchedCompositionPrism_naturality (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E) (x y z : D)
    (hp : (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Q.obj z)) :=
      dgPinchedCompositionTargetPoint_naturality A D E Q z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionPrism A D x y z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q) ≫
      (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hp)).hom =
      (Δ[1] ◁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map x y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map y z))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionPrism A E (Q.obj x) (Q.obj y) (Q.obj z) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  change ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hp)).hom.app _
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q)).app _
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionPrism A D x y z).app _ a))).val = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.roofSliceTransport_val hp]
  let σ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) x y).inv.app _ a.2.1).down
  let τ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) y z).inv.app _ a.2.2).down
  let σ' := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (Q.obj x) (Q.obj y)).inv.app _
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map x y)).app _ a.2.1)).down
  let τ' := ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomPinchedIso (R := A) (Q.obj y) (Q.obj z)).inv.app _
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map y z)).app _ a.2.2)).down
  let t := (SSet.stdSimplex.objEquiv a.1).toOrderHom
  change ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetSliceMap A D z).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSliceSimplex (C := ClosedCategory A D)
        (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y)
        (Z := ForgetEnrichment.of (Complex A) z) σ τ t)).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q =
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetSliceMap A E (Q.obj z)).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSliceSimplex (C := ClosedCategory A E)
        (X := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (Q.obj x))
        (Y := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (Q.obj y))
        (Z := ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (Q.obj z)) σ' τ' t)).val
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetSliceMap_val, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentTargetSliceMap_val]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSliceSimplex, Category.assoc, SSet.yonedaEquiv_symm_comp]
  have hσ : σ' = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap (Q.map x y) σ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardPinchedIso_inv_naturality (Q.map x y) a.2.1
  have hτ : τ' = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardSimplexMap (Q.map y z) τ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStandardPinchedIso_inv_naturality (Q.map y z) a.2.2
  rw [hσ, hτ]
  apply congrArg (fun s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A E (n + 1) => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm s)
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentSimplex_naturality Q _).trans
    (congrArg (fun s => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplex s) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgCoherentCompositionSimplex_naturality Q σ τ t))

lemma dgPinchedCompositionFamilyPrism_naturality (Q : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)
    {K : SSet.{max u v}} {x y z : D}
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D y z)
    (hp : (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex z) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q =
      (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A E)).symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (Q.obj z)) :=
      dgPinchedCompositionTargetPoint_naturality A D E Q z) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism A D f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map Q) ≫
      (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hp)).hom =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism A E
      (f ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map x y)) (g ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (Q.map y z)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPinchedCompositionFamilyPrism
  rw [Category.assoc, dgPinchedCompositionPrism_naturality A D E Q x y z hp]
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, CartesianMonoidalCategory.lift_map]
end SerrePositivity.InfinityCategories.Project.DerivedCategories

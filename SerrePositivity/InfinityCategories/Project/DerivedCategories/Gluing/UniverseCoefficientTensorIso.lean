module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoefficientTensorComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseNerveProjections
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseNerveComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UniverseDerivedStructure
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge
/-!
概要：元の係数脚と Yoneda 後の kernelTensor を、異なる対象宇宙でも実関手同型で比較する。
方針：全 Hom 自然な右単位同型の prism を共通単体宇宙で評価し、頂点辺の可逆性を移す。
規約：元の対象宇宙・双加群・右単位同型を保持し、Small は元 C・D のみとする。
使われ方：D-14 到着前の係数脚の接続と、一般宇宙での完全性の移送に用いる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded MonoidalCategory SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C] [Small.{u} C]
  (D : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] (M : _root_.SerrePositivity.DifferentialGraded.Bimodule R C D)
def dgGluingUniverseCoefficientTensorPrism :
    (SSet.uliftFunctor.{max (u + 1) v w, max u w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) ⊗ Δ[1] ⟶
      (SSet.uliftFunctor.{max (u + 1) v w, max (u + 1) v}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R C)) where
  app _ := ↾fun s => ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientTensorStrict R C D M).simplex
    s.1.down (SSet.stdSimplex.objEquiv s.2).toOrderHom)
  naturality _ _ f := by
    ext s
    apply ULift.ext
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientTensorStrict R C D M).simplex_pullback
      s.1.down (SSet.stdSimplex.objEquiv s.2).toOrderHom f.unop.toOrderHom

def dgGluingUniverseCoefficientTensorHomotopy :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, w, max (u + 1) v, max (u + 1) v w}
        ((_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseCoefficient R C D M) where
  h := dgGluingUniverseCoefficientTensorPrism R C D M
  h₀ := by
    ext n s
    apply ULift.ext
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    rfl
  h₁ := by
    ext n s
    apply ULift.ext
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
    rfl
  rel := by
    ext n s
    exact False.elim s.1.2

lemma dgGluingUniverseCoefficientTensorHomotopy_vertex_edge (d : D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (dgGluingUniverseCoefficientTensorHomotopy R C D M)
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex d))).edge =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{max (u + 1) v, max (u + 1) v w}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R C (BimoduleTensor.rightUnitIso R C D M d).hom).toTruncated).edge := by
  apply ULift.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplex1_ext
  · funext i
    fin_cases i <;> rfl
  · apply heq_of_eq
    change compose R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoefficientTensorStrict R C D M).app d).val
      ((((_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M)).map d d).f 0
        (_root_.SerrePositivity.DifferentialGraded.unitElement R d).val) (add_zero 0) = _
    rw [_root_.SerrePositivity.DifferentialGraded.DGFunctor.map_unitElement, _root_.SerrePositivity.DifferentialGraded.compose_unit]
    rfl

def dgGluingUniverseCoefficientTensorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, w, max (u + 1) v, max (u + 1) v w}
        ((_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseCoefficient R C D M) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy
    (dgGluingUniverseCoefficientTensorHomotopy R C D M) (by
      intro z
      obtain ⟨z⟩ := z
      obtain ⟨d, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective z
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
        (dgGluingUniverseCoefficientTensorHomotopy_vertex_edge R C D M d)).mpr
      apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IsInvertibleEdge.ulift
      have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge_isIso_of_homotopy R C
        (_root_.SerrePositivity.DifferentialGraded.BimoduleTensor.rightUnitIso R C D M d).hom (by infer_instance)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.edgeToPathHomotopyCategory _).map_isIso
        (SSet.Truncated.HomotopyCategory₂.homMk
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleEdge R C (BimoduleTensor.rightUnitIso R C D M d).hom).toTruncated))

def dgGluingUniverseCoefficientTensorCompositeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseYoneda.{u, w, v} R D ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
          (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseCoefficient R C D M) := by
  have he : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseYoneda.{u, w, v} R D ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
        (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, w, max (u + 1) v, max (u + 1) v w}
        ((_root_.SerrePositivity.DifferentialGraded.dgYoneda R D).comp (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M)) := by
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap_comp.{u, w, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
      (_root_.SerrePositivity.DifferentialGraded.dgYoneda R D) (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M)
  rw [he]
  exact dgGluingUniverseCoefficientTensorIso R C D M

def dgGluingUniverseDerivedCoefficientTensorCompositeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseYoneda.{u, w, v} R D ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseNerveMap.{u, max (u + 1) w, max (u + 1) v, max (u + 1) v w}
          (_root_.SerrePositivity.DifferentialGraded.Morita.kernelTensor R D C M)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseDerivedCoefficient R C D M) :=
  (dgGluingUniverseCoefficientTensorCompositeIso R C D M).postcomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUniverseModuleDerivedComparison.{u, v, w} R C)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing

module

public import SerrePositivity.KST.Spectra.D3ParameterDiagramTransformation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.D3DoubleEndpointJointFamily

/-!
概要：元のパラメータ単位子を、全パラメータ・全入力 Hom 上の coherent 比較にする。
方針：左右の単位自然同型を実パラメータ図式の豊穣変換へ送る。
規約：元の単位子の成分を変更せず、点ごとの同型で全自然性を代用しない。
使われ方：共同 loop 図式の厳密終点と元の端点パラメータ図式を照合する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
variable {J : Type} [Preorder J] (D : Jᵒᵖ ⥤ PointedSimplicialSet.{u})

/-- 左単位を付けた元の全パラメータ図式は、同じ左単位子で元の図式に自然同型。 -/
def d3ParameterLeftUnitIso : D ⋙ tensorLeft (𝟙_ PointedSimplicialSet.{u}) ≅ D :=
  NatIso.ofComponents (fun p ↦ λ_ (D.obj p)) (fun f ↦ leftUnitor_naturality (D.map f))

/-- 右単位を付けた元の全パラメータ図式も、同じ右単位子で自然同型。 -/
def d3ParameterRightUnitIso : D ⋙ tensorRight (𝟙_ PointedSimplicialSet.{u}) ≅ D :=
  NatIso.ofComponents (fun p ↦ ρ_ (D.obj p)) (fun f ↦ rightUnitor_naturality (D.map f))

/-- 元の左単位子を、順序パラメータと入力 Hom に同時に自然な coherent 比較へ送る。 -/
def d3ParameterLeftUnitFunctorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram
        (D ⋙ tensorLeft (𝟙_ PointedSimplicialSet.{u})))) :=
  d3ParameterPreFunctorIso (d3ParameterLeftUnitIso D)

/-- 元の右単位子も、同じ全パラメータ上の coherent 比較を与える。 -/
def d3ParameterRightUnitFunctorIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram D))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram
        (D ⋙ tensorRight (𝟙_ PointedSimplicialSet.{u})))) :=
  d3ParameterPreFunctorIso (d3ParameterRightUnitIso D)

section
local instance d3UnitSquareCategory : SmallCategory (Fin 2 × Fin 2) :=
  Preorder.smallCategory (Fin 2 × Fin 2)
local instance d3UnitProductCategory :
    SmallCategory ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) :=
  Preorder.smallCategory ((Fin 2 × Fin 2) × (Fin 2 × Fin 2))

/-- 第一パラメータの固定は、元の第二図式への左テンソルと自然同型。 -/
def d3BiParameterRightRestrictionIso
    (D E : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u}) (i j : Fin 2) :
    (d3BiParameterRightOrder i j).toFunctor.op ⋙ d3TensorParameter D E ≅
      E ⋙ tensorLeft (D.obj (Opposite.op (i, j))) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {p q} f ↦ by
    dsimp only [Iso.refl_hom]
    erw [Category.comp_id, Category.id_comp]
    change d3ParameterArrow D (le_rfl : (i, j) ≤ (i, j)) ⊗ₘ
      d3ParameterArrow E (leOfHom f.unop) = _
    rw [d3ParameterArrow_id D (i, j)]
    rfl)

/-- 第二パラメータの固定も、元の第一図式への右テンソルと自然同型。 -/
def d3BiParameterLeftRestrictionIso
    (D E : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u}) (i j : Fin 2) :
    (d3BiParameterLeftOrder i j).toFunctor.op ⋙ d3TensorParameter D E ≅
      D ⋙ tensorRight (E.obj (Opposite.op (i, j))) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun {p q} f ↦ by
    dsimp only [Iso.refl_hom]
    erw [Category.comp_id, Category.id_comp]
    change d3ParameterArrow D (leOfHom f.unop) ⊗ₘ
      d3ParameterArrow E (le_rfl : (i, j) ≤ (i, j)) = _
    rw [d3ParameterArrow_id E (i, j)]
    rfl)

/-- 第一方向の共同実終点を、元の左単位子でパラメータ全体上で比較する。 -/
def d3DoubleEndpointLeftTargetParameterIso :
    (d3BiParameterRightOrder 1 1).toFunctor.op ⋙ d3DoubleEndpointParameter.{u} ≅
      d3EndpointParameter :=
  d3BiParameterRightRestrictionIso d3EndpointParameter d3EndpointParameter 1 1 ≪≫
    d3ParameterLeftUnitIso d3EndpointParameter

/-- 第二方向でも、元の右単位子をパラメータ全体で同時に保持する。 -/
def d3DoubleEndpointRightTargetParameterIso :
    (d3BiParameterLeftOrder 1 1).toFunctor.op ⋙ d3DoubleEndpointParameter.{u} ≅
      d3EndpointParameter :=
  d3BiParameterLeftRestrictionIso d3EndpointParameter d3EndpointParameter 1 1 ≪≫
    d3ParameterRightUnitIso d3EndpointParameter

/-- 第一方向の同じパラメータ比較の成分は、元の左単位子そのもの。 -/
lemma d3DoubleEndpointLeftTargetParameterIso_hom_app
    (p : (Fin 2 × Fin 2)ᵒᵖ) :
    d3DoubleEndpointLeftTargetParameterIso.{u}.hom.app p =
      (λ_ (d3EndpointParameter.{u}.obj p)).hom := by
  simp only [d3DoubleEndpointLeftTargetParameterIso, Iso.trans_hom, NatTrans.comp_app,
    d3BiParameterRightRestrictionIso, d3ParameterLeftUnitIso, NatIso.ofComponents_hom_app,
    Iso.refl_hom]
  exact Category.id_comp _

/-- 第二方向も、元の右単位子の値を変更しない。 -/
lemma d3DoubleEndpointRightTargetParameterIso_hom_app
    (p : (Fin 2 × Fin 2)ᵒᵖ) :
    d3DoubleEndpointRightTargetParameterIso.{u}.hom.app p =
      (ρ_ (d3EndpointParameter.{u}.obj p)).hom := by
  simp only [d3DoubleEndpointRightTargetParameterIso, Iso.trans_hom, NatTrans.comp_app,
    d3BiParameterLeftRestrictionIso, d3ParameterRightUnitIso, NatIso.ofComponents_hom_app,
    Iso.refl_hom]
  exact Category.id_comp _

/-- 元の全パラメータ四角形の共同評価は、同じ順序円柱の同時評価そのもの。 -/
lemma d3ParameterSquare_joint
    (D : (Fin 2 × Fin 2)ᵒᵖ ⥤ PointedSimplicialSet.{u}) :
    (β_ PointedKanInfinity ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).hom ≫
      uncurry (d3PointedKanParameterSquare D) =
    d3PointedKanSquarePair ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram D) := by
  rw [d3PointedKanParameterSquare, uncurry_curry, ← Category.assoc,
    SymmetricCategory.symmetry, Category.id_comp]

/-- 第一方向共同族の厳密終点は、元の実終点パラメータの全共同評価。 -/
lemma d3DoubleEndpointJointLeft_target :
    d3DoubleEndpointJointLeftLoopFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 =
    d3PointedKanSquarePair ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram
      ((d3BiParameterRightOrder 1 1).toFunctor.op ⋙ d3DoubleEndpointParameter)) := by
  rw [d3DoubleEndpointJointLeftLoopFamily_corner, d3DoubleEndpointRightLoopFamily_ι,
    d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_right, d3ParameterSquare_joint]
  rfl

/-- 第二方向共同族も、元の指定実終点の全単体作用を厳密回収する。 -/
lemma d3DoubleEndpointJointRight_target :
    d3DoubleEndpointJointRightLoopFamily.{u} ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 =
    d3PointedKanSquarePair ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram
      ((d3BiParameterLeftOrder 1 1).toFunctor.op ⋙ d3DoubleEndpointParameter)) := by
  rw [d3DoubleEndpointJointRightLoopFamily_corner, d3DoubleEndpointLeftLoopFamily_ι,
    d3DoubleEndpointSquare, d3PointedKanBiParameterSquare_left, d3ParameterSquare_joint]
  rfl

/-- 第一方向の共同実終点へ、元の左単位を全パラメータで同時に保持して比較。 -/
def d3DoubleEndpointJointLeftTargetIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3PointedKanSquarePair ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter.{u}))
      (d3DoubleEndpointJointLeftLoopFamily ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3ParameterPreFunctorIso d3DoubleEndpointLeftTargetParameterIso).precomp
    d3PointedKanSquarePair) rfl d3DoubleEndpointJointLeft_target.symm

/-- 第二方向の共同実終点へも、元の右単位の全パラメータ比較を送る。 -/
def d3DoubleEndpointJointRightTargetIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (d3PointedKanSquarePair ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter.{u}))
      (d3DoubleEndpointJointRightLoopFamily ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3ParameterPreFunctorIso d3DoubleEndpointRightTargetParameterIso).precomp
    d3PointedKanSquarePair) rfl d3DoubleEndpointJointRight_target.symm
end

/-- 元の左単位比較を終点成分に指定した、一つの全パラメータ模型比較。 -/
def d3DoubleEndpointJointLeftUnitModelIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((d3PointedKanSquarePair ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter.{u})) ≫
      d3PointedKanLoopSection) d3DoubleEndpointJointLeftLoopFamily :=
  d3KanLoopDiagramIsoOverTarget _ _ d3DoubleEndpointJointLeftTargetIso

/-- 右単位についても、同じ共同実図式全体への模型比較を構成。 -/
def d3DoubleEndpointJointRightUnitModelIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((d3PointedKanSquarePair ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter.{u})) ≫
      d3PointedKanLoopSection) d3DoubleEndpointJointRightLoopFamily :=
  d3KanLoopDiagramIsoOverTarget _ _ d3DoubleEndpointJointRightTargetIso

/-- 左共同模型比較は、指定した全パラメータ単位比較を終点で厳密回収する。 -/
lemma d3DoubleEndpointJointLeftUnitModelIso_target :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointJointLeftUnitModelIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3KanCanonicalLoopFamily_target (d3PointedKanSquarePair ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter))) rfl =
    d3DoubleEndpointJointLeftTargetIso :=
  d3KanLoopDiagramIsoOverTarget_target _ _ _

/-- 右共同模型比較も、元の指定単位の全パラメータ比較を正確に回収する。 -/
lemma d3DoubleEndpointJointRightUnitModelIso_target :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3DoubleEndpointJointRightUnitModelIso.{u}.postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3KanCanonicalLoopFamily_target (d3PointedKanSquarePair ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanParameterDiagram d3EndpointParameter))) rfl =
    d3DoubleEndpointJointRightTargetIso :=
  d3KanLoopDiagramIsoOverTarget_target _ _ _

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

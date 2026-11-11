module

public import SerrePositivity.KST.Spectra.D3DoubleEndpointLoopFamilies
public import SerrePositivity.KST.Spectra.D3PointedKanLoopSection
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FullyFaithfulNormalizedIsoRecovery

/-!
概要：二方向の実 loop 全図式を、元のパラメータ単位子を終点成分に保って標準模型と比較。
方針：元の終点評価の充満忠実性で、指定した単位同型そのものを全図式へ持ち上げる。
規約：点ごとの対象同型から全関手比較を推論しない。保持済み模型単位との照合は別工程。
使われ方：二方向図式と既存標準模型の比較で、元の指定単位の値を失わないための界面。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

section
variable {A : SSet.{u + 1}} (F : A ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams PointedKanInfinity.{u})
  (g : A ⟶ PointedKanInfinity.{u})
  (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g (F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))

/-- 元の厳密 loop 切断へ指定終点関手を前合成した族は、同じ終点を厳密に保つ。 -/
lemma d3KanCanonicalLoopFamily_target :
    (g ≫ d3PointedKanLoopSection) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1 = g := by
  rw [Category.assoc, d3PointedKanLoopSection_target, Category.comp_id]

/-- 指定終点同型そのものを持ち上げた、標準全図式から実全図式への比較。 -/
def d3KanLoopDiagramIsoOverTarget : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ d3PointedKanLoopSection) F := by
  letI := d3PointedKanLoopEvaluation_trivial.{u}
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).preimageFunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e (d3KanCanonicalLoopFamily_target g).symm rfl)

/-- 同じ全図式比較の終点成分は、元の指定同型を正確に回収する。 -/
lemma d3KanLoopDiagramIsoOverTarget_target :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3KanLoopDiagramIsoOverTarget F g e).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3KanCanonicalLoopFamily_target g) rfl = e := by
  let := d3PointedKanLoopEvaluation_trivial.{u}
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1)).preimageNormalizedFunctorIso_postcomp_heq
      (g ≫ d3PointedKanLoopSection) F e (d3KanCanonicalLoopFamily_target g).symm rfl
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq_heq _ _ _).trans h)

/-- 同じ指定全図式比較と既存の通常 loop 単位から、始点の全関手比較を得る。 -/
def d3KanLoopDiagramSourceIsoOverTarget :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g ≫ pointedKanLoopInfinity) (F ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0) :=
  d3PointedKanLoopSection_sourceIso.precomp g ≪≫
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3KanLoopDiagramIsoOverTarget F g e).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 0 0)) (Category.assoc _ _ _) rfl
end

/-- 第一方向の実終点に使うのは、元の左パラメータ単位子の同じ全 Hom 同型。 -/
def d3DoubleEndpointLeftTargetIso (k l : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj.{u} (k, l))))
      (d3DoubleEndpointLeftLoopFamily k l ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (d3PointedKanPreFunctorIso (λ_ (d3EndpointParameterObj.{u} (k, l))).inv).symm
    rfl (d3DoubleEndpointLeftLoopFamily_corner k l 1 1).symm

/-- 第二方向でも、元の右パラメータ単位子の同じ指定値を終点に使う。 -/
def d3DoubleEndpointRightTargetIso (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj.{u} (i, j))))
      (d3DoubleEndpointRightLoopFamily i j ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq
    (d3PointedKanPreFunctorIso (ρ_ (d3EndpointParameterObj.{u} (i, j))).inv).symm
    rfl (d3DoubleEndpointRightLoopFamily_corner i j 1 1).symm

/-- 元の第一方向の実 loop 全図式を、指定単位を終点成分とする標準模型へ接続。 -/
def d3DoubleEndpointLeftModelIso (k l : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj.{u} (k, l))) ≫
      d3PointedKanLoopSection) (d3DoubleEndpointLeftLoopFamily k l) :=
  d3KanLoopDiagramIsoOverTarget _ _ (d3DoubleEndpointLeftTargetIso k l)

/-- 元の第二方向の実 loop 全図式も、指定単位を保持する同じ標準模型へ接続。 -/
def d3DoubleEndpointRightModelIso (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj.{u} (i, j))) ≫
      d3PointedKanLoopSection) (d3DoubleEndpointRightLoopFamily i j) :=
  d3KanLoopDiagramIsoOverTarget _ _ (d3DoubleEndpointRightTargetIso i j)

/-- 第一方向の模型比較は、元のパラメータ単位子を終点で厳密に回収する。 -/
lemma d3DoubleEndpointLeftModelIso_target (k l : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3DoubleEndpointLeftModelIso.{u} k l).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3KanCanonicalLoopFamily_target
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj (k, l))))) rfl =
    d3DoubleEndpointLeftTargetIso k l :=
  d3KanLoopDiagramIsoOverTarget_target _ _ _

/-- 第二方向の模型比較も、同じ右パラメータ単位子を終点で回収する。 -/
lemma d3DoubleEndpointRightModelIso_target (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq ((d3DoubleEndpointRightModelIso.{u} i j).postcomp
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation PointedKanInfinity 1 1))
      (d3KanCanonicalLoopFamily_target
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj (i, j))))) rfl =
    d3DoubleEndpointRightTargetIso i j :=
  d3KanLoopDiagramIsoOverTarget_target _ _ _

/-- 第一方向の同じ模型比較を始点評価した、元の通常 loop とテンソル模型の全関手同型。 -/
def d3DoubleEndpointLeftSourceIso (k l : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj.{u} (k, l))) ≫
      pointedKanLoopInfinity)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (endpointCircle.{u} ⊗
        d3EndpointParameterObj.{u} (k, l)))) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3KanLoopDiagramSourceIsoOverTarget _ _ (d3DoubleEndpointLeftTargetIso k l))
    rfl (d3DoubleEndpointLeftLoopFamily_corner k l 0 0)

/-- 第二方向の始点比較も、同じ実全図式から元の指定順序のテンソル模型へ得られる。 -/
def d3DoubleEndpointRightSourceIso (i j : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom (d3EndpointParameterObj.{u} (i, j))) ≫
      pointedKanLoopInfinity)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3PointedKanIhom
        (d3EndpointParameterObj.{u} (i, j) ⊗ endpointCircle.{u}))) :=
  _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (d3KanLoopDiagramSourceIsoOverTarget _ _ (d3DoubleEndpointRightTargetIso i j))
    rfl (d3DoubleEndpointRightLoopFamily_corner i j 0 0)

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

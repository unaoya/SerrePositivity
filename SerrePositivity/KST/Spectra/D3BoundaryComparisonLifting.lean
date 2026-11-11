module

public import SerrePositivity.KST.Spectra.D3BoundaryComparisonResolution
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace

/-!
概要：同じ比較・図式・厳密終点を保つ、境界付き相対 Hom の具体的持ち上げ問題。
方針：全頂点では元の恒等比較を固定し、相対関手 Hom の制限の指定頂点を持ち上げる。
規約：持ち上げの存在は未供給。解からの B は全単体の関手同型であり、hoFun だけでない。
使われ方：代替経路の必要な基礎入力を、単一の明示した可換四角形へ固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF
local instance boundaryLiftingSpectrumCategory : SimplicialCategory OmegaSpectrum.{u} :=
  OmegaSpectrum.simplicialCategory

private lemma discrete_restriction_eq {A X : SSet.{u}} (f g : A ⟶ X)
    (h : ∀ v, f.app (Opposite.op ⦋0⦌) v = g.app _ v) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι A ≫ g := by
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap_comp (𝟙 X) f (fun v ↦ f.app _ v) (fun _ ↦ rfl)
  have hg := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap_comp (𝟙 X) g (fun v ↦ g.app _ v) (fun _ ↦ rfl)
  rw [Category.comp_id] at hf hg
  rw [← hf, ← hg]
  congr 1
  funext v
  exact h v

/-- 元の全頂点上で固定する比較 path は、同じ refined 頂点の恒等 path そのもの。 -/
def boundaryComparisonVertexPath : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete (SimplicialNerve CommonObject.{u}) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath Sp :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl Sp

lemma boundaryComparisonVertexPath_endpoint (i : Fin 2) :
    boundaryComparisonVertexPath.{u} ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint Sp i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched := by
  unfold boundaryComparisonVertexPath
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun r : Sp.{u} ⟶ Sp ↦
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap commonRefinedEnriched) ≫ r)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint Sp i)).trans (Category.comp_id _))

/-- 元の同じ全頂点図式切断上で、元の恒等比較を付けた境界解。 -/
def boundaryComparisonVertexSection : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscrete (SimplicialNerve CommonObject.{u}) ⟶
    boundaryComparisonResolution :=
  pullback.lift boundaryComparisonVertexPath
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _ ≫ commonChosenLoopDiagramSection) (by
      apply CartesianMonoidalCategory.hom_ext
      · simp only [boundaryComparisonEndpoints, boundaryComparisonSourcePair, Category.assoc,
          lift_fst]
        rw [boundaryComparisonVertexPath_endpoint]
        rw [commonLoopDiagramRefinedMap, ← Category.assoc commonChosenLoopDiagramSection,
          commonChosenLoopDiagramSection_projection, Category.id_comp]
      · simp only [boundaryComparisonEndpoints, boundaryComparisonSourcePair, Category.assoc,
          lift_snd]
        rw [boundaryComparisonVertexPath_endpoint]
        rw [← Category.assoc commonChosenLoopDiagramSection,
          commonChosenLoopDiagramSection_family]
        exact discrete_restriction_eq _ _
          (fun v ↦ (commonChosenLoopSource_refined_vertex v).symm))

lemma boundaryComparisonVertexSection_projection :
    boundaryComparisonVertexSection.{u} ≫ boundaryComparisonProjection =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _ ≫ commonChosenLoopDiagramSection :=
  pullback.lift_snd _ _ _

/-- 必要な境界付き Hom 射影。全図式上の相対関手を、指定した全頂点上へ制限する。 -/
def boundaryComparisonHomRestriction :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace boundaryComparisonProjection.{u} commonChosenLoopDiagramSection ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace boundaryComparisonProjection
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _ ≫ commonChosenLoopDiagramSection) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPre _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _)

/-- 持ち上げる指定境界値は、上で構成した同じ恒等比較付き境界解の全関手頂点。 -/
def boundaryComparisonHomBoundary :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace boundaryComparisonProjection.{u}
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _ ≫ commonChosenLoopDiagramSection)) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorVertex _ _ boundaryComparisonVertexSection
    boundaryComparisonVertexSection_projection

/-- 必要な境界付き Hom の持ち上げ問題を明示する。零単体の解が全基底の比較を与える。 -/
theorem boundaryComparisonHomLiftSquare : CommSq
    (initial.to (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace boundaryComparisonProjection.{u}
      commonChosenLoopDiagramSection)) (initial.to (Δ[0] : SSet.{u + 1}))
    boundaryComparisonHomRestriction (SSet.yonedaEquiv.symm boundaryComparisonHomBoundary) :=
  ⟨initialIsInitial.hom_ext _ _⟩

/-- この指定 Hom 持ち上げの解を、同じ底と同じ境界を厳密に保つ全単体切断へ戻す。 -/
def boundaryComparisonSectionOfHomLift [boundaryComparisonHomLiftSquare.{u}.HasLift] :
    {s : SimplicialNerve CommonObject.{u} ⟶ boundaryComparisonResolution //
      s ≫ boundaryComparisonProjection = commonChosenLoopDiagramSection ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _ ≫ s = boundaryComparisonVertexSection} := by
  let x : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpace boundaryComparisonProjection
      commonChosenLoopDiagramSection (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι _)
      boundaryComparisonVertexSection boundaryComparisonVertexSection_projection) _⦋0⦌ :=
    ⟨SSet.yonedaEquiv boundaryComparisonHomLiftSquare.lift, by
      change boundaryComparisonHomRestriction.app _
        (SSet.yonedaEquiv boundaryComparisonHomLiftSquare.lift) =
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant boundaryComparisonHomBoundary 0
      rw [← SSet.yonedaEquiv_comp, boundaryComparisonHomLiftSquare.fac_right,
        Equiv.apply_symm_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]⟩
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorExtensionSpaceVertexEquiv _ _ _ _ _).symm x

/-- 明示した境界付き Hom 問題の解は、必要な全 Hom・全単体整合を持つ B の実値を与える。
この定義は持ち上げの存在を主張しない。最終結果へ新仮定として登録しない。 -/
def nativeLoopComparisonOfBoundaryHomLift [boundaryComparisonHomLiftSquare.{u}.HasLift] :
    NativeLoopComparison.{u} :=
  nativeLoopComparisonOfBoundarySection boundaryComparisonSectionOfHomLift.val
    boundaryComparisonSectionOfHomLift.property.1

end SerrePositivity.KST.Spectra.OmegaSpectrum.AdjointLoopRelativeBF

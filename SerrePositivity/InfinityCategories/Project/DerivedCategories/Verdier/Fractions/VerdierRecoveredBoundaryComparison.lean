module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeFunctorCoreRestriction
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.SimplexAttachmentEquivalences
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryPrefixPath
public import SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoreCylinder
public import SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSimplexCompletionComparison

/-!
概要：元の実境界円柱の商像と商余錐円柱の境界を、同じ二胞体を保持して全図式比較する。
方針：実前段左辺と元の分数比較辺の共有全経路を実代入し、相対 attachment へ直接貼る。
規約：次辺比較を Hom 類から選び直さず、元の分数評価二胞体の一次単体を保持する。
使われ方：指定した全境界比較を K 全体の比較へ延長する工程の実境界。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison
end SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}
  {G : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}

local notation "P" => S.toSSet ⊗ (Δ[1] : SSet)
local notation "J" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet) Δ[0]

/-- 同じ実前段辺と同じ分数比較辺を制限に持つ、実境界円柱の全図式比較。 -/
structure VerdierRecoveredBoundaryComparison
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f)
    (U : VerdierRecoveredQuotientCoconeCylinder r G) where
  edge : Truncated.Edge (X := (truncation 2).obj ((ihom J).obj ((ihom P).obj C.obj)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv P J C.obj
      (r.cylinder.homotopy.h ≫ (ihom J).map q.hom)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv P J C.obj ((S.ι ▷ Δ[1]) ≫ U.whole)))
  isInvertible : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom J).obj ((ihom P).obj C.obj)) edge
  prefix_eq : ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom P).obj C.obj)).app
      (Opposite.op ⦋1⦌) edge.edge =
    (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow r.cylinderSquare).map ((truncation 2).map
      ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))).edge)
  last_eq : ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app ((ihom P).obj C.obj)).app
      (Opposite.op ⦋1⦌) edge.edge =
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy).map ((truncation 2).map
      ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app ((ihom P).obj C.obj)))).edge)

/-- 回収済みの同じ二つの全円柱へ共有全経路を実代入し、指定二胞体を保持して貼る。 -/
lemma exists_verdierRecoveredBoundaryComparison
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f)
    (U : VerdierRecoveredQuotientCoconeCylinder r G) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv P J C.obj (r.cylinder.homotopy.h ≫ (ihom J).map q.hom)
  let T := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv P J C.obj ((S.ι ▷ Δ[1]) ≫ U.whole)
  let A₀ := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow r.cylinderSquare).map ((truncation 2).map
    ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))
  let B₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy).map
    ((truncation 2).map ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app ((ihom P).obj C.obj)))
  have hFp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ F =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv P Δ[n] B.obj
        (r.cylinder.homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj) ≫
        (ihom P).map q.hom := by
    dsimp only [F]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, Category.assoc,
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).naturality q.hom, ← Category.assoc]
    exact spanInternalHomFlip_post q.hom _
  have hTp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ T =
      (D ≫ q.hom) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap P C.obj := by
    dsimp only [T]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, Category.assoc, U.fixedPrefix,
      SSet.comp_const, spanInternalHomFlip_const]
    rfl
  have hAs : ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.cylinderSquare 0 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ F) := by
    rw [r.cylinderSquare_source]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv P Δ[n] B.obj
        (r.cylinder.homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj) ≫
        (ihom P).map q.hom) = _
    rw [hFp]
  have hAt : ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)).app
      (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.cylinderSquare 0 1) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0] ≫ T) := by
    rw [r.cylinderSquare_original]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap P B.obj) ≫ (ihom P).map q.hom) = _
    have hc := spanInternalHomFlip_post q.hom
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D) : P ⟶ (ihom (Δ[n] : SSet.{u})).obj B.obj)
    have hmap : ((ihom (Δ[n] : SSet.{u})).map q.hom).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex D) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D ≫ q.hom) := rfl
    rw [SSet.const_comp, hmap, spanInternalHomFlip_const, spanInternalHomFlip_const] at hc
    rw [hTp]
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex hc.symm
  let A' := (SSet.Edge.ofTruncated A₀).ofEq hAs hAt
  let V := r.boundary.h ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluationSquare h
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
  have hFn : r.cylinder.homotopy.h ≫ (ihom J).map q.hom ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (V ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C.obj) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app C.obj := by
    rw [(pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).naturality q.hom,
      ← Category.assoc, r.cylinder.homotopy_next]
    dsimp only [V]
    simp only [Category.assoc]
    have he := congrArg (fun g => r.boundary.h ≫ g ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app C.obj)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluationSquare_bottom h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    simp only [Category.assoc] at he
    rw [he]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow, Category.assoc]
    rw [(pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).naturality q.hom]
  have hTn : ((S.ι ▷ Δ[1]) ≫ U.whole) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (V ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge).app C.obj) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app C.obj := by
    dsimp only [V]
    simp only [Category.assoc]
    have he := congrArg (fun g => r.boundary.h ≫ g ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app C.obj)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluationSquare_top h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    simp only [Category.assoc] at he
    rw [he]
    simpa only [Category.assoc] using U.boundary_next
  have hFB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ F =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv P Δ[1] C.obj (V ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C.obj) := by
    dsimp only [F]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, Category.assoc, hFn,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  have hTB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ T =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv P Δ[1] C.obj (V ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge).app C.obj) := by
    dsimp only [T]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, hTn, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  have hBs : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv P Δ[1] C.obj (V ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C.obj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ F) := by
    rw [hFB]
  have hBt : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv P Δ[1] C.obj (V ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge).app C.obj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) ≫ T) := by
    rw [hTB]
  let B' := (SSet.Edge.ofTruncated B₀).ofEq hBs hBt
  have hab : SSet.yonedaEquiv.symm A'.edge ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app ((ihom P).obj C.obj) =
      SSet.yonedaEquiv.symm B'.edge ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])).app ((ihom P).obj C.obj) := by
    change SSet.yonedaEquiv.symm A₀.edge ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app ((ihom P).obj C.obj) =
      SSet.yonedaEquiv.symm (((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app ((ihom P).obj C.obj)).app
        (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy).edge) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0])).app ((ihom P).obj C.obj)
    rw [← SSet.yonedaEquiv_symm_comp, Category.assoc, ← NatTrans.comp_app,
      ← pre_map, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl]
    exact r.boundaryFractionComparison_sharedSource.symm
  obtain ⟨l, hlp, hln⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.exists_simplexAttachmentComparison n F T A'.toTruncated
    B'.toTruncated hab
  have hai : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj))
      A'.toTruncated :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := A₀) (f := A'.toTruncated) rfl).mp
      r.cylinderSquare_left_quotient_isInvertible
  have hbi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0])).obj ((ihom P).obj C.obj)) B'.toTruncated :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := B₀) (f := B'.toTruncated) rfl).mp
      (r.boundaryFractionComparison_isInvertible.map
        ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app ((ihom P).obj C.obj)))
  have hli := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentComparison_isInvertible n l
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hlp).mpr hai) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hln).mpr hbi)
  exact ⟨⟨l, hli, hlp, hln⟩⟩

def VerdierRecoveredBoundaryComparison.iso
    {r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f}
    {U : VerdierRecoveredQuotientCoconeCylinder r G}
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (r.cylinder.homotopy.h ≫ (ihom J).map q.hom) ((S.ι ▷ Δ[1]) ≫ U.whole) := by
  have := c.isInvertible
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorIsoUnflip (asIso (Truncated.HomotopyCategory.homMk c.edge))

namespace VerdierRecoveredBoundaryComparison

variable {r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f}
  {U : VerdierRecoveredQuotientCoconeCylinder r G}
  (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U)

lemma target_inverts (_c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges ((S.ι ▷ Δ[1]) ≫ U.whole) Set.univ := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertsAllEdges_toKan ((S.ι ▷ Δ[1]) ≫ U.coreWhole)).comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι
  simpa only [Category.assoc, U.coreWhole_ι] using hc

/-- 同じ全比較辺を、元の実 core 円柱と商 core 円柱の間の同じ全 prism に戻す。 -/
def coreHomotopy : SSet.Homotopy
    ((_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.relativeCylinder r) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q.hom J)
    ((S.ι ▷ Δ[1]) ≫ U.coreWhole) := by
  let H := spanFunctorEdgeUnflipCoreHomotopy c.edge c.isInvertible c.target_inverts
  have hF : (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.relativeCylinder r) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q.hom J =
      allEdgesCoreLift (r.cylinder.homotopy.h ≫ (ihom J).map q.hom)
        (spanFunctorEdgeUnflip_invertsAllEdges c.edge c.isInvertible c.target_inverts) := rfl
  have hG : allEdgesCoreLift ((S.ι ▷ Δ[1]) ≫ U.whole) c.target_inverts =
      (S.ι ▷ Δ[1]) ≫ U.coreWhole := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι).mp
    rw [allEdgesCoreLift_ι, Category.assoc, U.coreWhole_ι]
  exact { h := H.h, h₀ := H.h₀.trans hF.symm, h₁ := H.h₁.trans hG, rel := H.rel }

lemma coreHomotopy_ι : c.coreHomotopy.h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι =
    uncurry (SSet.yonedaEquiv.symm c.edge.edge ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso J P C.obj).hom) :=
  spanFunctorEdgeUnflipCoreHomotopy_ι c.edge c.isInvertible c.target_inverts

/-- 元の第一行商を始端とする全境界比較。円柱の二胞体と指定比較辺を選び直さない。 -/
def simplexQuotientHomotopy : SSet.Homotopy
    ((_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) ≫ relativeFirstRowSimplexQuotient q (n + 1))
    (((S.ι ▷ Δ[1]) ≫ U.coreWhole) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj)) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp c.coreHomotopy
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj))
  have hs : ((_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.relativeCylinder r) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q.hom J) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj) =
      (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) ≫ relativeFirstRowSimplexQuotient q (n + 1) := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι).mp
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι]
    rfl
  exact { h := H.h, h₀ := H.h₀.trans hs, h₁ := H.h₁, rel := H.rel }

lemma simplexQuotientHomotopy_ι : c.simplexQuotientHomotopy.h ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι =
    uncurry (SSet.yonedaEquiv.symm c.edge.edge ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.internalHomSwapIso J P C.obj).hom) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj := by
  change (c.coreHomotopy.h ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj)) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc, c.coreHomotopy_ι]

/-- 元の亜群化比較上の、構成済み境界二胞体から得られる同じ全関手同型。 -/
def completionComparisonIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (((_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap
      (relativeFirstRowSimplex q (n + 1) : SSet.{u})) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison q (n + 1))
    (((S.ι ▷ Δ[1]) ≫ U.coreWhole) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv).app C.obj)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison_unitIso q (n + 1)) (_root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.simplexCylinder r)
  exact e ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy c.simplexQuotientHomotopy

end VerdierRecoveredBoundaryComparison

/-- 元の有限商余錐族と実境界から、同じ両円柱と指定二胞体を保つ全境界比較を一括回収する。 -/
lemma exists_verdierFiniteCoconeBoundaryRecovery [K.Finite] [S.toSSet.Finite]
    (G : K ⟶ (ihom J).obj C.obj)
    (hG : G ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D ≫ q.hom)))
    (hz : G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const (q.hom.app (Opposite.op ⦋0⦌) z))
    (ha : a ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z =
      S.ι ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz) :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz),
      ∃ U : VerdierRecoveredQuotientCoconeCylinder r G,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) := by
  let fG := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanCoconeLastMapping (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz
  obtain ⟨r⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierFiniteMappingCoconeRecovery h D z S a fG ha
  have hGe := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanCoconeLastMapping_edge (D ≫ q.hom) (q.hom.app (Opposite.op ⦋0⦌) z) G hG hz
  obtain ⟨U⟩ := exists_verdierRecoveredQuotientCoconeCylinder r G hG hGe
  exact ⟨r, U, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierRecoveredBoundaryComparison r U⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SimplexTerminalPullbackFamily
public import SerrePositivity.KST.LocalizingInvariants.SimplexTerminalPullbackFamily
public import SerrePositivity.KST.LocalizingInvariants.TwoEndpointVerdierCoconeFamily

/-!
概要：元の実回収円柱から、一様な始端全族・正規化終端族・両端固定の全余錐円柱を構成する。
方針：両端の実構成と二脚照合を代入し、同じ二端点相対充填と attachment を実適用する。
規約：両端族・二脚一致・共有始域・円柱の存在を追加入力にしない。
使われ方：有限完成族の相対回収を、元の全単体図式の実相対輸送へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

local instance recoveredCylinderFiniteLimits {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable _

local instance recoveredCylinderParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory _ _

lemma terminalPullbackColumnFamily_const {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    (P : SSet.{u}) (s : (Δ[1] : SSet.{u}) ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalPullbackColumnFamily (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex s) : P ⟶ _) =
      SSet.const (terminalPullbackColumnVertex s) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj X) IsPullbackDiagramVertex).ι).mp
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalPullbackColumnFamily_ι, SSet.const_comp, SSet.const_comp]
  rfl

lemma uniformFiberPullbackFamily_terminal {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    (x z : B.obj _⦋0⦌) (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌)
    {K : SSet.{u}} {n : ℕ} (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x z) d)
    (F : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams B.obj)
    (hlast : F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      terminalPullbackColumnVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ d.val.val)) :
    parametricPullbackDiagramFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare K F)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_isPullback K F) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalPullbackColumnFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z
        (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x z) d)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_family, SSet.const_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex, hlast, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow_fiber,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalPullbackColumnFamily_const]

/-- 同じ実回収円柱から構成された、一様な全始端族と両端固定の全余錐円柱。 -/
structure VerdierRecoveredCoconeCylinder {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B)
    {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj) (z : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌)
    {S K : SSet.{u}} (j : S ⟶ K)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d)
    (a : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    (L : SSet.Homotopy (j ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d) a)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom (S ⊗ (Δ[1] : SSet.{u}))).obj B.obj))
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) where
  single : (Δ[n] : SSet.{u}) ⟶ pullbackDiagrams B.obj
  single_projection : single ≫ pullbackProjection B.obj = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.simplexTerminalCospanFamily D
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ d.val.val) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorDiagram_target i _ d)
  single_terminal : single.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
    terminalPullbackColumnVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ d.val.val)
  whole : K ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj
  whole_prefix : whole ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
    SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (single ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsPullbackDiagramVertex).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((stdSimplex.obj₀Equiv.symm (0 : Fin 2)),
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))))
  whole_next : whole ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
      (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d) ≫
        (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj
  whole_apex : whole ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z
  endSquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (ihom (Δ[n] : SSet.{u})).obj ((ihom S).obj B.obj)
  endSquare_pullback : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare endSquare
  endSquare_original : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex endSquare 0 1 =
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap S B.obj)
  endSquare_denominators : ∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : S _⦋0⦌),
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow (endSquare ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p)).edge ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i
  endCone : S ⟶ (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj
  end_prefix : endCone ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily (parametricPullbackDiagramFamily endSquare endSquare_pullback)
  end_next : endCone ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z a ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj
  end_apex : endCone ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z
  pullbacks : S ⊗ (Δ[1] : SSet.{u}) ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj)
  pullbacks_start : (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ pullbacks =
    SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex single)
  pullbacks_end : (SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫ pullbacks =
    parametricPullbackDiagramFamily endSquare endSquare_pullback
  pullbacks_projection : pullbacks ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj) =
    parametricPullbackDiagramFamily Q hQ ≫ (ihom (Δ[n] : SSet.{u})).map (pullbackProjection B.obj)
  pullbacks_terminal : pullbacks ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj) =
    parametricPullbackDiagramFamily Q hQ ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n)).app (pullbackDiagrams B.obj)
  homotopy : SSet.Homotopy (j ≫ whole) endCone
  homotopy_prefix : homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily pullbacks
  homotopy_next : homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z L.h ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj
  homotopy_apex : homotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z

/-- 元の実回収円柱の両端構成を実代入し、全余錐円柱を追加入力なしで構成する。 -/
lemma exists_verdierRecoveredCoconeCylinder
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌)
    (d : (verdierDenominatorOver i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌)
    {S K : SSet.{u}} (j : S ⟶ K)
    (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d)
    (a : S ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    (L : SSet.Homotopy (j ≫ g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) d) a)
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom (S ⊗ (Δ[1] : SSet.{u}))).obj B.obj))
    (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q)
    (hQr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ Q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv Δ[n] Δ[1]
      ((ihom (S ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (S ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z L.h)))))
    (hQt : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ Q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv Δ[n] Δ[1]
      ((ihom (S ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.simplexTerminalArrowFamily (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (S ⊗ Δ[1]) B.obj)))
    (hQl : Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (S ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z L.h))) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder i D z d j g a L Q hQ) := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  obtain ⟨F₀, hF₀p, hF₀l, h₀p, h₀t, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierRecoveredStartBoundary i D z d j g a L Q hQ hQr hQt hQl
  obtain ⟨R, hR, E, hRD, hRW, h₁p, h₁t, hEp, hEn, hEz⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierRecoveredEndBoundary h D z _ a L Q hQ hQr hQt hQl
  let FK := parametricPullbackDiagramFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare K F₀)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_isPullback K F₀)
  let FS := parametricPullbackDiagramFamily (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare S F₀)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_isPullback S F₀)
  have hFK := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformFiberPullbackFamily_terminal i x z d g F₀ hF₀l
  obtain ⟨W, hWp, hWn, hWz⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierSpanCoconeFamily i x z
    (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x z) d) FK hFK
  have hj : j ≫ FK = FS := by
    dsimp only [FK, FS]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_family, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_family,
      SSet.comp_const]
  have hCp : (j ≫ W) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily FS := by
    rw [Category.assoc, hWp, ← pullbackSourcePrefixFamily_pre, hj]
  have hCn : (j ≫ W) ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app B.obj =
      (SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow i x z L.h ≫
          (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app B.obj := by
    rw [Category.assoc, hWn, ← Category.assoc (SSet.ι₀ : S ⟶ S ⊗ Δ[1]),
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRecoveredBoundaryNumerator_start]
    simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyNumeratorArrow, Category.assoc]
    rfl
  have hG := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.parametricPullbackDiagramFamily_terminal_column Q hQ
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i x z L.h) hQl
  obtain ⟨F, U, hf₀, hf₁, hFp, hFt, hu₀, hu₁, hUp, hUn, hUz⟩ :=
    exists_twoEndpoint_verdierPullbackCoconeFamily i x z L.h
      (parametricPullbackDiagramFamily Q hQ) hG FS (parametricPullbackDiagramFamily R hR)
      h₀p h₁p h₀t h₁t (j ≫ W) E hCp hEp hCn hEn
  let H : SSet.Homotopy (j ≫ W) E := {
    h := U, h₀ := hu₀, h₁ := hu₁, rel := by
      apply SSet.hom_ext
      intro m
      apply ConcreteCategory.hom_ext
      intro v
      exact False.elim v.1.property }
  refine ⟨{
    single := F₀, single_projection := hF₀p, single_terminal := hF₀l, whole := W,
    whole_prefix := hWp.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_prefix K F₀),
    whole_next := hWn, whole_apex := hWz, endSquare := R, endSquare_pullback := hR,
    endSquare_original := hRD, endSquare_denominators := hRW,
    endCone := E, end_prefix := hEp, end_next := ?_, end_apex := hEz,
    pullbacks := F, pullbacks_start := ?_, pullbacks_end := hf₁,
    pullbacks_projection := hFp, pullbacks_terminal := hFt, homotopy := H,
    homotopy_prefix := hUp, homotopy_next := hUn, homotopy_apex := hUz }⟩
  · rw [hEn, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierRecoveredBoundaryNumerator_end]
  · rw [hf₀]
    dsimp only [FS]
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_family]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierRecoveredCoconeCylinder := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierRecoveredCoconeCylinder

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.recoveredCylinderFiniteLimits := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.recoveredCylinderFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.recoveredCylinderParameterFiniteLimits := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.recoveredCylinderParameterFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.terminalPullbackColumnFamily_const := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.terminalPullbackColumnFamily_const

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.uniformFiberPullbackFamily_terminal := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformFiberPullbackFamily_terminal

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.casesOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.endCone (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.endCone := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.endCone

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.endSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.endSquare := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.endSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.endSquare_denominators := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.endSquare_denominators

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.endSquare_original := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.endSquare_original

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.endSquare_pullback := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.endSquare_pullback

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.end_apex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.end_apex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.end_next := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.end_next

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.end_prefix := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.end_prefix

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.homotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.homotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.homotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.homotopy_apex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.homotopy_apex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.homotopy_next := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.homotopy_next

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.homotopy_prefix := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.homotopy_prefix

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.mk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.pullbacks (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.pullbacks := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.pullbacks

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.pullbacks_end := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.pullbacks_end

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.pullbacks_projection := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.pullbacks_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.pullbacks_start := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.pullbacks_start

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.pullbacks_terminal := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.pullbacks_terminal

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.rec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.recOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.single (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.single := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.single

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.single_projection := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.single_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.single_terminal := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.single_terminal

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.whole (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.whole := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.whole

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.whole_apex := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.whole_apex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.whole_next := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.whole_next

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.whole_prefix := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.whole_prefix

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredCoconeCylinder.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredCoconeCylinder.mk.sizeOf_spec

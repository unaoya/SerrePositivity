module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.PullbackFamilySquareRecovery
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierParametricSourceIso

/-!
概要：回収済みの実余錐円柱から、元の終端分母経路を保持する同じ実前段正方形を戻す。
方針：保存済みの二脚一致を逆転置へ代入し、同じ右辺と pullback 性で左辺の分母性を証明。
規約：実補完・余錐円柱・分母経路を選び直さず、全写像と一次単体を保持する。
使われ方：境界上の全比較に、元の実分数評価正方形と共有する源経路を供給する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

local instance cylinderSquareFiniteLimits {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable _

local instance cylinderSquareParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory _ _

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}

/-- 同じ実余錐円柱の補完済み pullback 全族から厳密に戻した全正方形。 -/
def VerdierFiniteMappingCoconeRecovery.cylinderSquare
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj) :=
  pullbackFamilySquare r.cylinder.pullbacks

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_isPullback
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare r.cylinderSquare := pullbackFamilySquare_isPullback _

/-- 元の実円柱の始端正方形は、保存済みの同じ一つの pullback 補完の一様正方形。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_start
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    r.cylinderSquare ≫ (ihom (Δ[n] : SSet.{u})).map
        ((pre (SSet.ι₀ : S.toSSet ⟶ S.toSSet ⊗ (Δ[1] : SSet.{u}))).app B.obj) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare S.toSSet r.cylinder.single := by
  change pullbackFamilySquare r.cylinder.pullbacks ≫ _ = _
  rw [← pullbackFamilySquare_pre_parameter, r.cylinder.pullbacks_start]
  have he := congrArg (fun F : S.toSSet ⟶ (ihom (Δ[n] : SSet.{u})).obj (pullbackDiagrams B.obj) =>
    pullbackFamilySquare F) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare_family S.toSSet r.cylinder.single)
  rw [pullbackFamilySquare_parametric] at he
  exact he.symm

/-- 元の実円柱の終端正方形も、保存済みの同じ正規化終端正方形に厳密一致する。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_end
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    r.cylinderSquare ≫ (ihom (Δ[n] : SSet.{u})).map
        ((pre (SSet.ι₁ : S.toSSet ⟶ S.toSSet ⊗ (Δ[1] : SSet.{u}))).app B.obj) =
      r.cylinder.endSquare := by
  change pullbackFamilySquare r.cylinder.pullbacks ≫ _ = _
  rw [← pullbackFamilySquare_pre_parameter, r.cylinder.pullbacks_end,
    pullbackFamilySquare_parametric]

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_right
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ r.cylinderSquare = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ r.square :=
  pullbackFamilySquare_right_eq _ _ _ r.cylinder.pullbacks_projection

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_top
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ r.cylinderSquare = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ r.square :=
  pullbackFamilySquare_top_eq _ _ _ r.cylinder.pullbacks_projection

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_original
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.cylinderSquare 0 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap (S.toSSet ⊗ (Δ[1] : SSet.{u})) B.obj) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ r.cylinderSquare).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) = _
  rw [r.cylinderSquare_top]
  exact r.square_original

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    r.cylinderSquare ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z r.boundary.h)) :=
  (pullbackFamilySquare_last_eq _ _ _ r.cylinder.pullbacks_terminal).trans r.square_terminal

/-- 同じ実前段の左辺は、終端で元の実分母経路そのものに厳密に一致する。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal_left
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ r.cylinderSquare ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z r.boundary.h) := by
  rw [r.cylinderSquare_terminal]
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareColumnDiagram, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, lift_snd,
    Category.id_comp]

lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_family
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    parametricPullbackDiagramFamily r.cylinderSquare r.cylinderSquare_isPullback =
      r.cylinder.pullbacks := by
  have : Mono ((ihom (Δ[n] : SSet.{u})).map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj B.obj)
        IsPullbackDiagramVertex).ι) := (ihom (Δ[n] : SSet.{u})).map_mono _
  apply (cancel_mono ((ihom (Δ[n] : SSet.{u})).map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices ((ihom ((Δ[1] : SSet.{u}) ⊗ Δ[1])).obj B.obj)
      IsPullbackDiagramVertex).ι)).mp
  rw [parametricPullbackDiagramFamily_ι]
  exact pullbackFamilySquare_family r.cylinder.pullbacks

/-- 戻した同じ正方形の始域全族は、回収済み実余錐円柱の全前段そのもの。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_prefix
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily
      (parametricPullbackDiagramFamily r.cylinderSquare r.cylinderSquare_isPullback) =
      r.cylinder.homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj := by
  rw [r.cylinderSquare_family]
  exact r.cylinder.homotopy_prefix.symm

/-- 別の補完を選ばず、同じ実円柱前段の全左辺が元の分母であることを証明する。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_denominators
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f)
    (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : (S.toSSet ⊗ (Δ[1] : SSet.{u})) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow (r.cylinderSquare ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p)).edge ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i := by
  have hK := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff r.cylinderSquare).mp r.cylinderSquare_isPullback k
  have hP := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff (r.cylinderSquare ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)).mp hK p
  have hK' := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff r.square).mp r.square_pullback k
  have hP' := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPullbackSquare_functor_iff (r.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k)).mp hK' p
  apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_pullback_iff h _ hP).mpr
  have hw := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences_pullback_iff h _ hP').mp (r.square_denominators k p)
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (r.cylinderSquare ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ (r.square ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p) := by
    simpa only [Category.assoc] using
      congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p) r.cylinderSquare_right
  simpa only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareRightArrow_edge, Category.assoc, hr] using hw

/-- 元の同じ実円柱前段の転置は、復元した正方形の始域頂点に厳密に一致する。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_source
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.cylinderSquare 0 0 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[n] B.obj
        (r.cylinder.homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj)) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily_parametric r.cylinderSquare r.cylinderSquare_isPullback
  rw [r.cylinderSquare_prefix] at hs
  have ht := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[n] B.obj) hs
  have hh := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv Δ[n] (S.toSSet ⊗ (Δ[1] : SSet.{u})) B.obj).symm_apply_apply
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)).symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.cylinderSquare 0 0))
  have ht' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[n] B.obj
      (r.cylinder.homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)).symm
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex r.cylinderSquare 0 0) := ht.trans hh
  exact ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ht').trans
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)).apply_symm_apply
      _)).symm

/-- 同じ実左辺の商像自身が可逆であり、別の比較辺の存在で代用しない。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_isInvertible
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge
      (X := (ihom (Δ[n] : SSet.{u})).obj
        ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj C.obj))
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow r.cylinderSquare).map ((truncation 2).map
        ((ihom (Δ[n] : SSet.{u})).map
          ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom)))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceEdge_isInvertible h r.cylinderSquare r.cylinderSquare_denominators

/-- 可逆と証明した同じ実左辺の終端成分は、元の全分母経路の同じ商像。 -/
lemma VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_terminal
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj C.obj)
      (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌)
      (((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow r.cylinderSquare).map ((truncation 2).map
        ((ihom (Δ[n] : SSet.{u})).map
          ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom)))).edge) =
      SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyDenominatorArrow i
            (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z r.boundary.h) ≫
          (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom) := by
  have hn : (ihom (Δ[n] : SSet.{u})).map
        ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) ≫
        (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom := rfl
  change ((ihom (Δ[n] : SSet.{u})).map
      ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n))).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow r.cylinderSquare).edge = _
  rw [hn, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_edge, ← SSet.yonedaEquiv_comp]
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ r.cylinderSquare ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) ≫
      (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom) = _
  apply congrArg SSet.yonedaEquiv
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ (ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).map q.hom)
    r.cylinderSquare_terminal_left

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.cylinderSquareFiniteLimits := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cylinderSquareFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.cylinderSquareParameterFiniteLimits := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.cylinderSquareParameterFiniteLimits

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_denominators := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_denominators

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_end := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_end

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_family := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_family

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_isPullback := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_isPullback

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_isInvertible := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_isInvertible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_terminal := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_left_quotient_terminal

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_original := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_original

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_prefix := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_prefix

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_right := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_source := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_start := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_start

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal_left := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_terminal_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinderSquare_top := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinderSquare_top

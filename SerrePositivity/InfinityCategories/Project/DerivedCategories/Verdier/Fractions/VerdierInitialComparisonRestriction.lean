module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison

/-!
概要：同じ K 始端全比較と指定 S 始端全比較の両制限を、元の一次単体で照合する。
方針：前段は同じ補完左辺と始端全正方形、次辺は同じ分数二胞体の自然性で証明する。
規約：両制限一致を新仮定にせず、指定された元の二つの全比較辺を保持する。
使われ方：K 始端比較を指定 S 比較へ合わせる相対 attachment Homotopy 延長の入力。
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
namespace SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison
end SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison
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

lemma VerdierFiniteMappingCoconeRecovery.initialPrefixSquareRestriction
    (r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    r.cylinderSquare ≫ (ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom) ≫
      (ihom (Δ[n] : SSet.{u})).map ((pre (SSet.ι₀ : S.toSSet ⟶ P)).app C.obj) =
    terminalRefinementSquare r.cylinder.single ≫ (ihom (Δ[n] : SSet.{u})).map
      (q.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap S.toSSet C.obj) := by
  rw [← Functor.map_comp, (pre (SSet.ι₀ : S.toSSet ⟶ P)).naturality q.hom,
    Functor.map_comp, ← Category.assoc, r.cylinderSquare_start,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.uniformTerminalRefinementSquare, Category.assoc, ← Functor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_postcomp]

namespace VerdierRecoveredInitialComparison

variable {r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f}
  {U : VerdierRecoveredQuotientCoconeCylinder r G}
  (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U)

/-- 元の前段比較一次単体は、K 始端側と指定 S 始端側の制限で厳密に一致する。 -/
lemma boundary_prefix_eq :
    ((ihom (Δ[n] : SSet.{u})).map ((pre (SSet.ι₀ : S.toSSet ⟶ P)).app C.obj)).app
      (Opposite.op ⦋1⦌)
      (((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom P).obj C.obj)).app
        (Opposite.op ⦋1⦌) b.edge.edge) =
    ((ihom (Δ[n] : SSet.{u})).map ((pre S.ι).app C.obj)).app (Opposite.op ⦋1⦌)
      (((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) c.edge.edge) := by
  rw [b.prefix_eq, c.prefix_eq]
  change ((ihom (Δ[n] : SSet.{u})).map ((pre (SSet.ι₀ : S.toSSet ⟶ P)).app C.obj)).app
      (Opposite.op ⦋1⦌)
      (((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow r.cylinderSquare).edge) =
    ((ihom (Δ[n] : SSet.{u})).map ((pre S.ι).app C.obj)).app (Opposite.op ⦋1⦌)
      (((ihom (Δ[n] : SSet.{u})).map (q.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K C.obj)).app
        (Opposite.op ⦋1⦌) c.denominator.edge)
  rw [c.denominator_edge]
  simp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_edge, ← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  have he := congrArg (fun Q => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ Q) r.initialPrefixSquareRestriction
  simpa only [Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_precomp] using he

/-- 元の分数評価二胞体の比較一次単体も、両始端全比較の次辺制限で厳密に一致する。 -/
lemma boundary_last_eq :
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0])).map
      ((pre (SSet.ι₀ : S.toSSet ⟶ P)).app C.obj)).app (Opposite.op ⦋1⦌)
      (((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app ((ihom P).obj C.obj)).app
        (Opposite.op ⦋1⦌) b.edge.edge) =
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0])).map ((pre S.ι).app C.obj)).app (Opposite.op ⦋1⦌)
      (((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) c.edge.edge) := by
  rw [b.last_eq, c.last_eq]
  change (((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app ((ihom P).obj C.obj)) ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0])).map
        ((pre (SSet.ι₀ : S.toSSet ⟶ P)).app C.obj)).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy).edge =
    (((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)) ≫
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0])).map ((pre S.ι).app C.obj)).app (Opposite.op ⦋1⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy r.initialFractionHomotopy).edge
  rw [← (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).naturality,
    ← (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).naturality]
  exact congrArg
    (fun e => ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom).app ((ihom S.toSSet).obj C.obj)).app
      (Opposite.op ⦋1⦌) e) r.boundaryFractionComparison_start

end VerdierRecoveredInitialComparison
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.initialPrefixSquareRestriction := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.initialPrefixSquareRestriction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.boundary_last_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.boundary_last_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.boundary_prefix_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.boundary_prefix_eq

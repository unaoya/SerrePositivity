module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredInitialComparison

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
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}

local notation "P" => S.toSSet ⊗ (Δ[1] : SSet)

lemma VerdierFiniteMappingCoconeRecovery.initialPrefixSquareRestriction
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    r.cylinderSquare ≫ (ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom) ≫
      (ihom (Δ[n] : SSet.{u})).map ((pre (SSet.ι₀ : S.toSSet ⟶ P)).app C.obj) =
    terminalRefinementSquare r.cylinder.single ≫ (ihom (Δ[n] : SSet.{u})).map
      (q.hom ≫ constantFunctorMap S.toSSet C.obj) := by
  rw [← Functor.map_comp, (pre (SSet.ι₀ : S.toSSet ⟶ P)).naturality q.hom,
    Functor.map_comp, ← Category.assoc, r.cylinderSquare_start,
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.uniformTerminalRefinementSquare, Category.assoc, ← Functor.map_comp,
    constantFunctorMap_postcomp]

namespace VerdierRecoveredInitialComparison
open _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredInitialComparison
variable {r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f}
  {U : VerdierRecoveredQuotientCoconeCylinder r G}
  (c : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredInitialComparison r U) (b : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U)

/-- 元の前段比較一次単体は、K 始端側と指定 S 始端側の制限で厳密に一致する。 -/
lemma boundary_prefix_eq :
    ((ihom (Δ[n] : SSet.{u})).map ((pre (SSet.ι₀ : S.toSSet ⟶ P)).app C.obj)).app
      (Opposite.op ⦋1⦌)
      (((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom P).obj C.obj)).app
        (Opposite.op ⦋1⦌) b.edge.edge) =
    ((ihom (Δ[n] : SSet.{u})).map ((pre S.ι).app C.obj)).app (Opposite.op ⦋1⦌)
      (((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) c.edge.edge) := by
  rw [b.prefix_eq, c.prefix_eq]
  change ((ihom (Δ[n] : SSet.{u})).map ((pre (SSet.ι₀ : S.toSSet ⟶ P)).app C.obj)).app
      (Opposite.op ⦋1⦌)
      (((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)).app (Opposite.op ⦋1⦌)
        (squareLeftArrow r.cylinderSquare).edge) =
    ((ihom (Δ[n] : SSet.{u})).map ((pre S.ι).app C.obj)).app (Opposite.op ⦋1⦌)
      (((ihom (Δ[n] : SSet.{u})).map (q.hom ≫ constantFunctorMap K C.obj)).app
        (Opposite.op ⦋1⦌) c.denominator.edge)
  rw [c.denominator_edge]
  simp only [squareLeftArrow_edge, ← SSet.yonedaEquiv_comp]
  apply congrArg SSet.yonedaEquiv
  have he := congrArg (fun Q => squareLeftEdge ≫ Q) r.initialPrefixSquareRestriction
  simpa only [Category.assoc, ← Functor.map_comp, constantFunctorMap_precomp] using he

/-- 元の分数評価二胞体の比較一次単体も、両始端全比較の次辺制限で厳密に一致する。 -/
lemma boundary_last_eq :
    ((ihom (join (Δ[0] : SSet.{u}) Δ[0])).map
      ((pre (SSet.ι₀ : S.toSSet ⟶ P)).app C.obj)).app (Opposite.op ⦋1⦌)
      (((pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app ((ihom P).obj C.obj)).app
        (Opposite.op ⦋1⦌) b.edge.edge) =
    ((ihom (join (Δ[0] : SSet.{u}) Δ[0])).map ((pre S.ι).app C.obj)).app (Opposite.op ⦋1⦌)
      (((pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app ((ihom K).obj C.obj)).app
        (Opposite.op ⦋1⦌) c.edge.edge) := by
  rw [b.last_eq, c.last_eq]
  change (((pre (joinStdSimplexIso 0 0).hom).app ((ihom P).obj C.obj)) ≫
      (ihom (join (Δ[0] : SSet.{u}) Δ[0])).map
        ((pre (SSet.ι₀ : S.toSSet ⟶ P)).app C.obj)).app (Opposite.op ⦋1⦌)
        (functorEdgeOfSimplicialHomotopy r.boundaryFractionHomotopy).edge =
    (((pre (joinStdSimplexIso 0 0).hom).app ((ihom K).obj C.obj)) ≫
      (ihom (join (Δ[0] : SSet.{u}) Δ[0])).map ((pre S.ι).app C.obj)).app (Opposite.op ⦋1⦌)
        (functorEdgeOfSimplicialHomotopy r.initialFractionHomotopy).edge
  rw [← (pre (joinStdSimplexIso 0 0).hom).naturality,
    ← (pre (joinStdSimplexIso 0 0).hom).naturality]
  exact congrArg
    (fun e => ((pre (joinStdSimplexIso 0 0).hom).app ((ihom S.toSSet).obj C.obj)).app
      (Opposite.op ⦋1⦌) e) r.boundaryFractionComparison_start

end VerdierRecoveredInitialComparison
end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.initialPrefixSquareRestriction := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.initialPrefixSquareRestriction

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.boundary_last_eq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredInitialComparison.boundary_last_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.boundary_prefix_eq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredInitialComparison.boundary_prefix_eq

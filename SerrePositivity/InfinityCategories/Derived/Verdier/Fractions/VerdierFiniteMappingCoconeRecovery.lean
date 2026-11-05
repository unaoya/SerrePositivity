module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredCoconeCylinder

/-!
概要：元の有限商 Hom 族を、実分母・次辺・全余錐円柱と元の商比較円柱を保持して回収する。
方針：Sp-6 s4 の相対回収を実適用し、構成済み両端族を二端点貼合せへ全て代入する。
規約：実分母・前段補完・両端族・円柱・二脚一致を追加入力にしない。
使われ方：元の第一行単体比較に必要な相対有限全族の実入力。
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
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

local instance mappingCoconeFiniteLimits {X : SSet.{u}} [Quasicategory X] [IsStable X] :
    HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance mappingCoconeParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [IsStable X] : HasFiniteLimits ((ihom P).obj X) :=
  hasFiniteLimits_functorCategory _ _

/-- 元の有限商 Hom 族の実回収と、同じ境界・同じ商比較を保つ全余錐円柱の証人。 -/
structure VerdierFiniteMappingCoconeRecovery
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌) {K : SSet.{u}} (S : K.Subcomplex)
    (a : S.toSSet ⟶ verdierDenominatorSpanFamily i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    (f : K ⟶ intervalMappingSpace
      (q.hom.app (Opposite.op ⦋0⦌)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
      (q.hom.app (Opposite.op ⦋0⦌) z)) where
  denominator : (verdierDenominatorOver i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) : SSet.{u}) _⦋0⦌
  numerator : K ⟶ vertexFiber (verdierDenominatorSpanProjection i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) denominator
  boundary : SSet.Homotopy
    (S.ι ≫ numerator ≫ vertexFiberι (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) denominator) a
  comparison : SSet.Homotopy
    (numerator ≫ vertexFiberι (verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) denominator ≫
      verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) f
  comparison_boundary : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ comparison.h = boundary.h ≫
    verdierDenominatorSpanCanonicalComparison i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
    fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z
  square : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    (ihom (Δ[n] : SSet.{u})).obj ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
  square_pullback : IsPullbackSquare square
  square_original : squareVertex square 0 1 =
    functorVertex (D ≫ constantFunctorMap (S.toSSet ⊗ Δ[1]) B.obj)
  square_right : squareRightEdge ≫ square = internalHomFlipHomEquiv Δ[n] Δ[1]
    ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
    (SSet.const (functorVertex (internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
      (verdierSpanFamilyDenominatorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z boundary.h))))
  square_top : squareTopEdge ≫ square = internalHomFlipHomEquiv Δ[n] Δ[1]
    ((ihom (S.toSSet ⊗ (Δ[1] : SSet.{u}))).obj B.obj)
    (simplexTerminalArrowFamily (D ≫ constantFunctorMap (S.toSSet ⊗ Δ[1]) B.obj))
  square_terminal : square ≫ evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (Fin.last n)) =
    squareColumnDiagram (internalHomFlipHomEquiv (S.toSSet ⊗ (Δ[1] : SSet.{u})) Δ[1] B.obj
      (verdierSpanFamilyDenominatorArrow i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z boundary.h))
  square_denominators : ∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌)
      (p : (S.toSSet ⊗ (Δ[1] : SSet.{u})) _⦋0⦌),
    (squareLeftArrow (square ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
      weakEquivalences i
  cylinder : VerdierRecoveredCoconeCylinder i D z denominator S.ι numerator a boundary
    square square_pullback

/-- 有限商 Hom 族と元の実境界から、両端族を実代入した全余錐円柱まで回収する。 -/
lemma exists_verdierFiniteMappingCoconeRecovery
    {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
    (h : IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌) {K : SSet.{u}} [K.Finite] (S : K.Subcomplex) [S.toSSet.Finite]
    (a : S.toSSet ⟶ verdierDenominatorSpanFamily i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
    (f : K ⟶ intervalMappingSpace
      (q.hom.app (Opposite.op ⦋0⦌)
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
      (q.hom.app (Opposite.op ⦋0⦌) z))
    (ha : a ≫ verdierDenominatorSpanCanonicalComparison i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z = S.ι ≫ f) :
    Nonempty (VerdierFiniteMappingCoconeRecovery h D z S a f) := by
  obtain ⟨d, g, L, G, hG, Q, hQ, hD, hl, _, hr, ht, hW⟩ :=
    exists_verdierRelativeMappingBoundaryRefinement h D z S a f ha
  rw [verdierDenominatorFamilyEdge_span] at hr hl
  obtain ⟨U⟩ := exists_verdierRecoveredCoconeCylinder h D z d S.ι g a L Q hQ hr ht hl
  exact ⟨{
    denominator := d, numerator := g, boundary := L, comparison := G,
    comparison_boundary := hG, square := Q, square_pullback := hQ,
    square_original := hD, square_right := hr, square_top := ht,
    square_terminal := hl, square_denominators := hW, cylinder := U }⟩

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierFiniteMappingCoconeRecovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierFiniteMappingCoconeRecovery

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.mappingCoconeFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.mappingCoconeFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.mappingCoconeParameterFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.mappingCoconeParameterFiniteLimits

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.boundary (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.boundary := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.casesOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.comparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.comparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.comparison_boundary := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.comparison_boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.ctorIdx := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinder (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.cylinder := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.cylinder

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.denominator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.denominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.denominator

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.mk := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.noConfusionType := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.numerator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.numerator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.numerator

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.rec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.recOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.square (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.square := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.square

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.square_denominators := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.square_denominators

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.square_original := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.square_original

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.square_pullback := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.square_pullback

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.square_right := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.square_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.square_terminal := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.square_terminal

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.square_top := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.square_top

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.mk.inj := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.mk.injEq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.mk.sizeOf_spec

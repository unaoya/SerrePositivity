module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexDenominators
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeCoconeAttachment

/-!
概要：元の分母精密化の全前段を、商後合成で元の定値図式へ比較する。
方針：実正方形の同じ左辺を二重の点ごとの可逆性判定で反転し、全族へ転置する。
規約：分母性は元の各実左辺のものを使い、パラメータに有限性を要求しない。
使われ方：実境界円柱の商像を元の strict core に戻すための全辺反転。
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

local instance parametricSourceFiniteLimits {X : SSet.{u}} [Quasicategory X]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_of_isStable _

local instance parametricSourceParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits ((ihom P).obj X) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasFiniteLimits_functorCategory _ _

lemma pullbackSourcePrefixFamily_parametric {P X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X]
    {n : ℕ} (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj X)) (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily (parametricPullbackDiagramFamily Q hQ) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv Δ[n] P X
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom P).obj X)).symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 0)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily, Functor.map_comp, ← Category.assoc,
    parametricPullbackDiagramFamily_ι, parametricPullbackSquares_vertex]
  rfl

/-- 元の実正方形の同じ左辺自身は、各成分が分母なら商後合成で可逆になる。 -/
lemma verdierParametricSourceEdge_isInvertible
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) {n : ℕ} {P : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj))
    (hW : ∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : P _⦋0⦌),
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p)).edge ∈
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj))
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow Q).map ((truncation 2).map
        ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))) := by
  let F₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 0)
  let F₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 1)
  let e : SSet.Edge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₁) :=
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow Q)).ofEq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).apply_symm_apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 0)).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).apply_symm_apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 1)).symm
  let eQ : Truncated.Edge
      (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F₀ ≫ (ihom P).map q.hom)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F₁ ≫ (ihom P).map q.hom)) :=
    e.toTruncated.map ((truncation 2).map
      ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj)) eQ := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt eQ).mpr
    intro k
    let ek₀ := eQ.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k))
    let f₀k := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv P C.obj).symm
      ((F₀ ≫ (ihom P).map q.hom).app (Opposite.op ⦋0⦌) k)
    let f₁k := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv P C.obj).symm
      ((F₁ ≫ (ihom P).map q.hom).app (Opposite.op ⦋0⦌) k)
    let ek : Truncated.Edge (X := (truncation 2).obj ((ihom P).obj C.obj))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f₀k) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f₁k) :=
      ((SSet.Edge.ofTruncated ek₀).ofEq
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex k _).trans
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv P C.obj).apply_symm_apply _).symm)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex k _).trans
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv P C.obj).apply_symm_apply _).symm)).toTruncated
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := ek) (f := ek₀) rfl).mp
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt ek).mpr
    intro p
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := ek.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p)))
      (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p)).edge).map
          ((truncation 2).map q.hom)) rfl).mpr (h.inverts (hW k p))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := eQ)
    (f := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow Q).map ((truncation 2).map
      ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))) rfl).mp hi

/-- 元の同じ左辺の全成分が分母なら、その全前段の商像は元の定値図式と同型。 -/
def verdierParametricSourceIso
    {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    {P : SSet.{u}} (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj)) (hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare Q)
    (hD : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 1 = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap P B.obj))
    (hW : ∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : P _⦋0⦌),
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow (Q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt p)).edge ∈
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily (parametricPullbackDiagramFamily Q hQ) ≫
        (ihom (Δ[n] : SSet.{u})).map q.hom)
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (D ≫ q.hom)) : P ⟶ _) := by
  let F₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 0)
  let F₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).symm (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 1)
  let e : SSet.Edge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F₁) :=
    (SSet.Edge.ofTruncated (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow Q)).ofEq
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).apply_symm_apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 0)).symm
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).apply_symm_apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareVertex Q 0 1)).symm
  let eQ : Truncated.Edge
      (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F₀ ≫ (ihom P).map q.hom)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F₁ ≫ (ihom P).map q.hom)) :=
    e.toTruncated.map ((truncation 2).map
      ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj)) eQ :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := eQ)
      (f := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareLeftArrow Q).map ((truncation 2).map
        ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))) rfl).mpr
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceEdge_isInvertible h Q hW)
  have := hi
  let ef : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (F₀ ≫ (ihom P).map q.hom) (F₁ ≫ (ihom P).map q.hom) :=
    asIso (Truncated.HomotopyCategory.homMk eQ)
  have he := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorIsoFlip ef
  rw [spanInternalHomFlip_post q.hom F₀, spanInternalHomFlip_post q.hom F₁] at he
  have hF₁ : F₁ = D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap P B.obj := by
    dsimp only [F₁]
    rw [hD]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).symm_apply_apply _
  rw [hF₁, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.flip_postcompose_constant, SSet.const_comp] at he
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily_parametric Q hQ]
  exact he

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.parametricSourceFiniteLimits := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.parametricSourceFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.parametricSourceParameterFiniteLimits := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.parametricSourceParameterFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.pullbackSourcePrefixFamily_parametric := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.pullbackSourcePrefixFamily_parametric

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceEdge_isInvertible := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceEdge_isInvertible

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_10 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_11 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_12 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_13 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_13

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_7 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_8 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_9 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierParametricSourceIso._proof_9

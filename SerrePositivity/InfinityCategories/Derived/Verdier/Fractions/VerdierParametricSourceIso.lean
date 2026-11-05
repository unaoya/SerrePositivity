module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexDenominators
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRelativeCoconeAttachment

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
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

local instance parametricSourceFiniteLimits {X : SSet.{u}} [Quasicategory X]
    [IsStable X] : HasFiniteLimits X := hasFiniteLimits_of_isStable _

local instance parametricSourceParameterFiniteLimits {X P : SSet.{u}}
    [Quasicategory X] [IsStable X] : HasFiniteLimits ((ihom P).obj X) :=
  hasFiniteLimits_functorCategory _ _

lemma pullbackSourcePrefixFamily_parametric {P X : SSet.{u}} [Quasicategory X] [IsStable X]
    {n : ℕ} (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj X)) (hQ : IsPullbackSquare Q) :
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily (parametricPullbackDiagramFamily Q hQ) =
      internalHomFlipHomEquiv Δ[n] P X
        ((functorVertexEquiv Δ[n] ((ihom P).obj X)).symm (squareVertex Q 0 0)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily, Functor.map_comp, ← Category.assoc,
    parametricPullbackDiagramFamily_ι, parametricPullbackSquares_vertex]
  rfl

/-- 元の実正方形の同じ左辺自身は、各成分が分母なら商後合成で可逆になる。 -/
lemma verdierParametricSourceEdge_isInvertible
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) {n : ℕ} {P : SSet.{u}}
    (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj))
    (hW : ∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : P _⦋0⦌),
      (squareLeftArrow (Q ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
        _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) :
    IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj))
      ((squareLeftArrow Q).map ((truncation 2).map
        ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))) := by
  let F₀ := (functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).symm (squareVertex Q 0 0)
  let F₁ := (functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).symm (squareVertex Q 0 1)
  let e : SSet.Edge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj))
      (functorVertex F₀) (functorVertex F₁) :=
    (SSet.Edge.ofTruncated (squareLeftArrow Q)).ofEq
    ((functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).apply_symm_apply (squareVertex Q 0 0)).symm
    ((functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).apply_symm_apply (squareVertex Q 0 1)).symm
  let eQ : Truncated.Edge
      (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj)))
      (functorVertex (F₀ ≫ (ihom P).map q.hom)) (functorVertex (F₁ ≫ (ihom P).map q.hom)) :=
    e.toTruncated.map ((truncation 2).map
      ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))
  have hi : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj)) eQ := by
    apply (isInvertibleEdge_iff_evaluateFunctorAt eQ).mpr
    intro k
    let ek₀ := eQ.map ((truncation 2).map (evaluateFunctorAt k))
    let f₀k := (functorVertexEquiv P C.obj).symm
      ((F₀ ≫ (ihom P).map q.hom).app (Opposite.op ⦋0⦌) k)
    let f₁k := (functorVertexEquiv P C.obj).symm
      ((F₁ ≫ (ihom P).map q.hom).app (Opposite.op ⦋0⦌) k)
    let ek : Truncated.Edge (X := (truncation 2).obj ((ihom P).obj C.obj))
        (functorVertex f₀k) (functorVertex f₁k) :=
      ((SSet.Edge.ofTruncated ek₀).ofEq
        ((evaluateFunctorAt_functorVertex k _).trans
          ((functorVertexEquiv P C.obj).apply_symm_apply _).symm)
        ((evaluateFunctorAt_functorVertex k _).trans
          ((functorVertexEquiv P C.obj).apply_symm_apply _).symm)).toTruncated
    apply (isInvertibleEdge_congr (e := ek) (f := ek₀) rfl).mp
    apply (isInvertibleEdge_iff_evaluateFunctorAt ek).mpr
    intro p
    exact (isInvertibleEdge_congr (e := ek.map ((truncation 2).map (evaluateFunctorAt p)))
      (f := (edgeOfSimplex
        (squareLeftArrow (Q ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge).map
          ((truncation 2).map q.hom)) rfl).mpr (h.inverts (hW k p))
  exact (isInvertibleEdge_congr (e := eQ)
    (f := (squareLeftArrow Q).map ((truncation 2).map
      ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))) rfl).mp hi

/-- 元の同じ左辺の全成分が分母なら、その全前段の商像は元の定値図式と同型。 -/
def verdierParametricSourceIso
    {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
    (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    {P : SSet.{u}} (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
      (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj)) (hQ : IsPullbackSquare Q)
    (hD : squareVertex Q 0 1 = functorVertex (D ≫ constantFunctorMap P B.obj))
    (hW : ∀ (k : (Δ[n] : SSet.{u}) _⦋0⦌) (p : P _⦋0⦌),
      (squareLeftArrow (Q ≫ evaluateFunctorAt k ≫ evaluateFunctorAt p)).edge ∈
        _root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) :
    FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily (parametricPullbackDiagramFamily Q hQ) ≫
        (ihom (Δ[n] : SSet.{u})).map q.hom)
      (SSet.const (functorVertex (D ≫ q.hom)) : P ⟶ _) := by
  let F₀ := (functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).symm (squareVertex Q 0 0)
  let F₁ := (functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).symm (squareVertex Q 0 1)
  let e : SSet.Edge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj B.obj))
      (functorVertex F₀) (functorVertex F₁) :=
    (SSet.Edge.ofTruncated (squareLeftArrow Q)).ofEq
    ((functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).apply_symm_apply (squareVertex Q 0 0)).symm
    ((functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).apply_symm_apply (squareVertex Q 0 1)).symm
  let eQ : Truncated.Edge
      (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj)))
      (functorVertex (F₀ ≫ (ihom P).map q.hom)) (functorVertex (F₁ ≫ (ihom P).map q.hom)) :=
    e.toTruncated.map ((truncation 2).map
      ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))
  have hi : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom P).obj C.obj)) eQ :=
    (isInvertibleEdge_congr (e := eQ)
      (f := (squareLeftArrow Q).map ((truncation 2).map
        ((ihom (Δ[n] : SSet.{u})).map ((ihom P).map q.hom)))) rfl).mpr
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceEdge_isInvertible h Q hW)
  have := hi
  let ef : FunctorIso (F₀ ≫ (ihom P).map q.hom) (F₁ ≫ (ihom P).map q.hom) :=
    asIso (Truncated.HomotopyCategory.homMk eQ)
  have he := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanFunctorIsoFlip ef
  rw [spanInternalHomFlip_post q.hom F₀, spanInternalHomFlip_post q.hom F₁] at he
  have hF₁ : F₁ = D ≫ constantFunctorMap P B.obj := by
    dsimp only [F₁]
    rw [hD]
    exact (functorVertexEquiv Δ[n] ((ihom P).obj B.obj)).symm_apply_apply _
  rw [hF₁, F2.Presentable.flip_postcompose_constant, SSet.const_comp] at he
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily_parametric Q hQ]
  exact he

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.parametricSourceFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.parametricSourceFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.parametricSourceParameterFiniteLimits := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.parametricSourceParameterFiniteLimits

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.pullbackSourcePrefixFamily_parametric := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.pullbackSourcePrefixFamily_parametric

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceEdge_isInvertible := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceEdge_isInvertible

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_10 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_10

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_11 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_11

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_12 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_12

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_13 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_13

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_7 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_7

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_8 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_8

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierParametricSourceIso._proof_9 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierParametricSourceIso._proof_9

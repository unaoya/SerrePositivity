module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeFunctorCoreRestriction
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreComparison
public import SerrePositivity.KST.LocalizingInvariants.VerdierFiniteSimplexCoconeFamilyLift
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSimplexCompletionComparison

/-!
概要：有限余錐族の実分母精密化を、元の strict core 逆像と同じ商射へ戻す。
方針：元の全比較辺を転置し、その同じ prism を core 内へ厳密に回収する。
規約：前段比較辺・頂点の恒等経路を保持し、core 比較の代表辺を選び直さない。
使われ方：第一行単体商の亜群化比較に対する有限全族の実供給。
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
namespace SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift
end SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

/-- 元の core 商族の、指定比較一次単体と両制限を保持する実精密化。 -/
structure VerdierFiniteCoreCoconeFamilyLift {B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C) {K : SSet.{u}} {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌)
    (G : K ⟶ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) : SSet.{u})) where
  source : (Δ[n] : SSet.{u}) ⟶ B.obj
  denominator : Truncated.Edge
    (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
    (functorVertex _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.source) (functorVertex D)
  denominator_mem : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.denominator.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)
  family : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj
  prefix_eq : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.family ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
    SSet.const (functorVertex _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.source)
  apex : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.family ≫ evaluateFunctorAt
    ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z
  comparison : Truncated.Edge
    (X := (truncation 2).obj ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj ((ihom K).obj C.obj)))
    (functorVertex (internalHomFlipHomEquiv K (join (Δ[n] : SSet.{u}) Δ[0]) C.obj
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.family ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom)))
    (functorVertex (internalHomFlipHomEquiv K (join (Δ[n] : SSet.{u}) Δ[0]) C.obj
      (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι)))
  comparison_invertible : IsInvertibleEdge
    (X := (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj ((ihom K).obj C.obj)) _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.comparison
  comparison_prefix : ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)).app
    (Opposite.op ⦋1⦌) _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.comparison.edge = (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge K q.hom _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.denominator).edge
  comparison_apex : SSet.yonedaEquiv.symm _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.comparison.edge ≫
    (pre (joinInr (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj) =
    curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫
      SSet.const (functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌) z) : K ⟶ C.obj)))

variable {B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C} {K : SSet.{u}} {n : ℕ}
  {D : (Δ[n] : SSet.{u}) ⟶ B.obj} {z : B.obj _⦋0⦌}
  {G : K ⟶ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) : SSet.{u})}

namespace VerdierFiniteCoreCoconeFamilyLift
open _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift
variable (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift q D z G)

lemma target_inverts (_r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift q D z G) : InvertsEdges
    (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι) Set.univ := by
  intro e _
  exact (isInvertibleEdge_congr (e := (edgeOfSimplex e).map ((truncation 2).map
    (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι)))
    (f := edgeOfSimplex (G.app (Opposite.op ⦋1⦌) e).val) rfl).mpr
      ((quasicategoryCore_mem_edge_iff _).mp (G.app (Opposite.op ⦋1⦌) e).property)

lemma family_inverts : InvertsEdges
    (r.family ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) Set.univ :=
  spanFunctorEdgeUnflip_invertsAllEdges r.comparison r.comparison_invertible r.target_inverts

/-- 元の実全族を、同じ商後合成の strict core 逆像内で回収する。 -/
def relativeFamily : K ⟶ (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.relativeFunctorCore q.hom (join (Δ[n] : SSet.{u}) Δ[0]) : SSet.{u}) :=
  corePreimageLift ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) r.family r.family_inverts

lemma relativeFamily_ι : r.relativeFamily ≫
    (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.relativeFunctorCore q.hom (join (Δ[n] : SSet.{u}) Δ[0])).ι = r.family := rfl

/-- 元の strict core 逆像の商射を始端とし、指定商族を終端とする同じ比較 prism。 -/
def quotientHomotopy : SSet.Homotopy
    (r.relativeFamily ≫ _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.relativeFunctorCoreQuotient q.hom (join (Δ[n] : SSet.{u}) Δ[0])) G := by
  let H := spanFunctorEdgeUnflipCoreHomotopy r.comparison r.comparison_invertible r.target_inverts
  have hF : r.relativeFamily ≫ _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.relativeFunctorCoreQuotient q.hom
      (join (Δ[n] : SSet.{u}) Δ[0]) =
      allEdgesCoreLift (r.family ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom)
        r.family_inverts := rfl
  have hG : allEdgesCoreLift
      (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι)
        r.target_inverts = G := by
    apply (cancel_mono (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι).mp
    rw [allEdgesCoreLift_ι]
  exact { h := H.h, h₀ := H.h₀.trans hF.symm, h₁ := H.h₁.trans hG, rel := H.rel }

/-- 比較の全単体写像は、元の指定一次単体の転置をそのまま uncurry したもの。 -/
lemma quotientHomotopy_ι : r.quotientHomotopy.h ≫
    (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι =
    uncurry (SSet.yonedaEquiv.symm r.comparison.edge ≫
      (internalHomSwapIso (join (Δ[n] : SSet.{u}) Δ[0]) K C.obj).hom) :=
  spanFunctorEdgeUnflipCoreHomotopy_ι r.comparison r.comparison_invertible r.target_inverts

/-- join 座標の同じ実全族を、元の第一行の標準単体座標に戻す。 -/
def simplexFamily : K ⟶ (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  corePreimageLift ((ihom (Δ[n + 1] : SSet.{u})).map q.hom)
    (r.family ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj) (by
      rw [Category.assoc, ← (pre (joinStdSimplexIso n 0).inv).naturality q.hom,
        ← Category.assoc]
      exact r.family_inverts.comp ((pre (joinStdSimplexIso n 0).inv).app C.obj))

lemma simplexFamily_ι : r.simplexFamily ≫ (relativeFirstRowSimplex q (n + 1)).ι =
    r.family ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj := rfl

/-- 第一行の元の商射から指定商族への比較は、同じ全 prism の座標変換。 -/
def simplexQuotientHomotopy : SSet.Homotopy
    (r.simplexFamily ≫ relativeFirstRowSimplexQuotient q (n + 1))
    (G ≫ quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)) := by
  let H := functorHomotopyPostcomp r.quotientHomotopy
    (quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj))
  have hs : (r.relativeFamily ≫ _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.relativeFunctorCoreQuotient q.hom
      (join (Δ[n] : SSet.{u}) Δ[0])) ≫
      quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj) =
      r.simplexFamily ≫ relativeFirstRowSimplexQuotient q (n + 1) := by
    apply (cancel_mono (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι).mp
    change (r.family ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) ≫
        (pre (joinStdSimplexIso n 0).inv).app C.obj =
      (r.family ≫ (pre (joinStdSimplexIso n 0).inv).app B.obj) ≫
        (ihom (Δ[n + 1] : SSet.{u})).map q.hom
    rw [Category.assoc, (pre (joinStdSimplexIso n 0).inv).naturality q.hom,
      ← Category.assoc]
  exact { h := H.h, h₀ := H.h₀.trans hs, h₁ := H.h₁, rel := H.rel }

/-- 元の第一行比較の全 prism も、指定一次単体の転置と座標変換そのもの。 -/
lemma simplexQuotientHomotopy_ι : r.simplexQuotientHomotopy.h ≫
    (quasicategoryCore ((ihom (Δ[n + 1] : SSet.{u})).obj C.obj)).ι =
    uncurry (SSet.yonedaEquiv.symm r.comparison.edge ≫
      (internalHomSwapIso (join (Δ[n] : SSet.{u}) Δ[0]) K C.obj).hom) ≫
        (pre (joinStdSimplexIso n 0).inv).app C.obj := by
  change (r.quotientHomotopy.h ≫
    quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)) ≫ _ = _
  rw [Category.assoc, quasicategoryCoreMap_ι, ← Category.assoc, r.quotientHomotopy_ι]

/-- 元の同じ実全族を、第一行の亜群化単位で完成する。 -/
def completedSimplexFamily :
    K ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  r.simplexFamily ≫ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (relativeFirstRowSimplex q (n + 1) : SSet.{u})

/-- 元の亜群化比較の有限余錐族回収。全 Hom の充満忠実性は別の証明義務。 -/
def completionComparisonIso : FunctorIso
    (r.completedSimplexFamily ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison q (n + 1))
    (G ≫ quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)) := by
  have e := FunctorIso.precomp
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.relativeFirstRowSimplexCompletionComparison_unitIso q (n + 1)) r.simplexFamily
  exact e ≪≫ functorIsoOfSimplicialHomotopy r.simplexQuotientHomotopy

end VerdierFiniteCoreCoconeFamilyLift

/-- 有限商余錐族を、元の strict core 逆像と同じ商射の全族比較まで実回収する。 -/
lemma exists_verdierFiniteCoreCoconeFamilyLift
    {A : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q) [K.Finite]
    (hG : (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι) ≫
      (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)))
    (hz : (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι) ≫
      evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) =
      SSet.const (q.hom.app (Opposite.op ⦋0⦌) z)) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift q D z G) := by
  obtain ⟨D', t, F, l, ht, hF, hA, hi, hp, hv, _⟩ :=
    exists_verdierFiniteSimplexCoconeFamilyLift h D z
      (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι) hG hz
  exact ⟨⟨D', t, ht, F, hF, hA, l, hi, hp, hv⟩⟩

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierFiniteCoreCoconeFamilyLift := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierFiniteCoreCoconeFamilyLift

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift._sizeOf_inst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.apex := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.apex

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.casesOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.comparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.comparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.comparison_apex := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.comparison_apex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.comparison_invertible := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.comparison_invertible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.comparison_prefix := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.comparison_prefix

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.completedSimplexFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.completedSimplexFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.completedSimplexFamily

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.completionComparisonIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.completionComparisonIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.completionComparisonIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.ctorIdx := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.denominator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.denominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.denominator

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.denominator_mem := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.denominator_mem

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.family (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.family := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.family

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.family_inverts := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.family_inverts

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.mk := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.noConfusionType := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.noConfusionType

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.prefix_eq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.prefix_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy_ι := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.rec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.recOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.relativeFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.relativeFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.relativeFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.relativeFamily_ι := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.relativeFamily_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.simplexFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.simplexFamily_ι := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexFamily_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy_ι := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.source (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.source := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.target_inverts := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.target_inverts

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.completionComparisonIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.completionComparisonIso._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.mk.inj := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.mk.injEq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_5 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_6 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.quotientHomotopy._proof_6

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.simplexFamily._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexFamily._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteCoreCoconeFamilyLift.simplexQuotientHomotopy._proof_4

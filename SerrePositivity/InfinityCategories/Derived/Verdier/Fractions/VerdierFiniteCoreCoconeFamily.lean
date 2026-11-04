module

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
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 元の core 商族の、指定比較一次単体と両制限を保持する実精密化。 -/
structure VerdierFiniteCoreCoconeFamilyLift {B C : StableCategory.{u}}
    (q : ExactMap B C) {K : SSet.{u}} {n : ℕ} (D : (Δ[n] : SSet.{u}) ⟶ B.obj)
    (z : B.obj _⦋0⦌)
    (G : K ⟶ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) : SSet.{u})) where
  source : (Δ[n] : SSet.{u}) ⟶ B.obj
  denominator : Truncated.Edge
    (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
    (functorVertex source) (functorVertex D)
  denominator_mem : denominator.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌)
  family : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj B.obj
  prefix_eq : family ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app B.obj =
    SSet.const (functorVertex source)
  apex : family ≫ evaluateFunctorAt
    ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) = SSet.const z
  comparison : Truncated.Edge
    (X := (truncation 2).obj ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj ((ihom K).obj C.obj)))
    (functorVertex (internalHomFlipHomEquiv K (join (Δ[n] : SSet.{u}) Δ[0]) C.obj
      (family ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom)))
    (functorVertex (internalHomFlipHomEquiv K (join (Δ[n] : SSet.{u}) Δ[0]) C.obj
      (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι)))
  comparison_invertible : IsInvertibleEdge
    (X := (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj ((ihom K).obj C.obj)) comparison
  comparison_prefix : ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj)).app
    (Opposite.op ⦋1⦌) comparison.edge = (spanConstantPrefixEdge K q.hom denominator).edge
  comparison_apex : SSet.yonedaEquiv.symm comparison.edge ≫
    (pre (joinInr (Δ[n] : SSet.{u}) Δ[0])).app ((ihom K).obj C.obj) =
    curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫
      SSet.const (functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌) z) : K ⟶ C.obj)))

variable {B C : StableCategory.{u}} {q : ExactMap B C} {K : SSet.{u}} {n : ℕ}
  {D : (Δ[n] : SSet.{u}) ⟶ B.obj} {z : B.obj _⦋0⦌}
  {G : K ⟶ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj) : SSet.{u})}

namespace VerdierFiniteCoreCoconeFamilyLift
variable (r : VerdierFiniteCoreCoconeFamilyLift q D z G)

lemma target_inverts (_r : VerdierFiniteCoreCoconeFamilyLift q D z G) : InvertsEdges
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
def relativeFamily : K ⟶ (relativeFunctorCore q.hom (join (Δ[n] : SSet.{u}) Δ[0]) : SSet.{u}) :=
  corePreimageLift ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) r.family r.family_inverts

lemma relativeFamily_ι : r.relativeFamily ≫
    (relativeFunctorCore q.hom (join (Δ[n] : SSet.{u}) Δ[0])).ι = r.family := rfl

/-- 元の strict core 逆像の商射を始端とし、指定商族を終端とする同じ比較 prism。 -/
def quotientHomotopy : SSet.Homotopy
    (r.relativeFamily ≫ relativeFunctorCoreQuotient q.hom (join (Δ[n] : SSet.{u}) Δ[0])) G := by
  let H := spanFunctorEdgeUnflipCoreHomotopy r.comparison r.comparison_invertible r.target_inverts
  have hF : r.relativeFamily ≫ relativeFunctorCoreQuotient q.hom
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
  have hs : (r.relativeFamily ≫ relativeFunctorCoreQuotient q.hom
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
    K ⟶ groupoidCompletion (relativeFirstRowSimplex q (n + 1) : SSet.{u}) :=
  r.simplexFamily ≫ groupoidCompletionMap (relativeFirstRowSimplex q (n + 1) : SSet.{u})

/-- 元の亜群化比較の有限余錐族回収。全 Hom の充満忠実性は別の証明義務。 -/
def completionComparisonIso : FunctorIso
    (r.completedSimplexFamily ≫ relativeFirstRowSimplexCompletionComparison q (n + 1))
    (G ≫ quasicategoryCoreMap ((pre (joinStdSimplexIso n 0).inv).app C.obj)) := by
  have e := FunctorIso.precomp
    (relativeFirstRowSimplexCompletionComparison_unitIso q (n + 1)) r.simplexFamily
  exact e ≪≫ functorIsoOfSimplicialHomotopy r.simplexQuotientHomotopy

end VerdierFiniteCoreCoconeFamilyLift

/-- 有限商余錐族を、元の strict core 逆像と同じ商射の全族比較まで実回収する。 -/
lemma exists_verdierFiniteCoreCoconeFamilyLift
    {A : StableCategory.{u}} {i : ExactMap A B} (h : IsVerdierSequence i q) [K.Finite]
    (hG : (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι) ≫
      (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (D ≫ q.hom)))
    (hz : (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι) ≫
      evaluateFunctorAt ((joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) =
      SSet.const (q.hom.app (Opposite.op ⦋0⦌) z)) :
    Nonempty (VerdierFiniteCoreCoconeFamilyLift q D z G) := by
  obtain ⟨D', t, F, l, ht, hF, hA, hi, hp, hv, _⟩ :=
    exists_verdierFiniteSimplexCoconeFamilyLift h D z
      (G ≫ (quasicategoryCore ((ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj)).ι) hG hz
  exact ⟨⟨D', t, ht, F, hF, hA, l, hi, hp, hv⟩⟩

end SerrePositivity.KST.LocalizingInvariants

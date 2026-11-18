import SerrePositivity.AlgebraicGeometry.ArcRouteB.AicProductArc
import SerrePositivity.AlgebraicGeometry.ArcRouteB.AicValuationArc
import SerrePositivity.AlgebraicGeometry.ArcRouteB.ArcCoverCech
import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeArrowComparison
import SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison
import SerrePositivity.AlgebraicGeometry.ArcRouteB.CoverLaws
import SerrePositivity.AlgebraicGeometry.ArcRouteB.Definitions
import SerrePositivity.AlgebraicGeometry.ArcRouteB.EndpointSections
import SerrePositivity.AlgebraicGeometry.ArcRouteB.FilteredUniversalCech
import SerrePositivity.AlgebraicGeometry.ArcRouteB.FpResiduePoint
import SerrePositivity.AlgebraicGeometry.ArcRouteB.FrobeniusPerfect
import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalCoefficientPerfect
import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalGluing
import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalPoints
import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalRestrictions
import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalSpectrum
import SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalTensorComparison
import SerrePositivity.AlgebraicGeometry.ArcRouteB.LocalExtensions
import SerrePositivity.AlgebraicGeometry.ArcRouteB.ModelUnder
import SerrePositivity.AlgebraicGeometry.ArcRouteB.OverlapCoefficientDetection
import SerrePositivity.AlgebraicGeometry.ArcRouteB.OverlapComplex
import SerrePositivity.AlgebraicGeometry.ArcRouteB.OverlapShortExact
import SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedFpArc
import SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedModelCocone
import SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedModelColimit
import SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedModelDiagram
import SerrePositivity.AlgebraicGeometry.ArcRouteB.ProbeComparison
import SerrePositivity.AlgebraicGeometry.ArcRouteB.ProbeTerms
import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalCech
import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalOverlap
import SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalUltraproduct
import Lean.Util.CollectAxioms

/-!
2iの小さい所有宣言監査と、利用側の型の確認。
CanonicalArcRouteBConsumerの定義は正本drafts/A6/ArcRouteB.leanからそのまま抜き出した。
既存の未完成drafts全体をimportせず、同じ出口の型を実際にLeanで照合する。
所有モジュール内のprivate・生成補助も含め、標準三公理以外を拒否する。
-/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity
namespace CanonicalArcRouteBConsumer
/-- ArcSheafProperty.lean と同じ、指定した階数で試す被覆族。 -/
def ValuativeCoverFamily (rank : CommRingCat.{u} → Prop)
    {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ∀ (V : CommRingCat.{u}) [IsDomain V] [ValuationRing V], rank V → ∀ k : A →+* V,
    ∃ (i : ι) (W : CommRingCat.{u}) (hW : IsDomain W),
      letI : IsDomain W := hW
      ValuationRing W ∧ rank W ∧ ∃ (e : V →+* W) (l : B i →+* W),
        e.FaithfullyFlat ∧ l.comp (f i) = e.comp k

/-- 有限族の v 被覆（BS17 Definition 2.1）。 -/
def IsVCoverFamily {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ValuativeCoverFamily (fun _ => True) B f

/-- 標数 p で使う有限族の arc 被覆（BM18 Definition 1.2）。 -/
def IsArcCoverFamilyCharP {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) : Prop :=
  ValuativeCoverFamily (fun V => ringKrullDim V ≤ 1) B f

/-- 有限族を積への一射にして作る増大 Čech 余脈体。 -/
def affineFamilyCech {A : Type u} [CommRing A] {ι : Type u} [Finite ι]
    (B : ι → Type u) [∀ i, CommRing (B i)] (f : ∀ i, A →+* B i) :
    CosimplicialObject.Augmented CommRingCat.{u} :=
  (Arrow.mk (CommRingCat.ofHom (RingHom.pi f))).augmentedCechConerve

/-- B6 が閉じる G-A6-1 の型（BS 著者版 Proposition 8.10 の証明）。
有限族の型と次数の規約は元の下書きに合わせている。 -/
def ArcRouteBGoal (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ {A : Type u} [CommRing A] [CharP A p] [PerfectRing A p]
    {ι : Type u} [Finite ι] (B : ι → Type u) [∀ i, CommRing (B i)]
    [∀ i, CharP (B i) p] [∀ i, PerfectRing (B i) p]
    (f : ∀ i, A →+* B i), IsArcCoverFamilyCharP B f →
    Cech.AugmentedRingCechExact (affineFamilyCech B f)


example (p : ℕ) [Fact p.Prime] : ArcRouteBGoal.{u} p :=
  SerrePositivity.AlgebraicGeometry.ArcRouteB.cech_exact_of_arcCover_perfect p
end CanonicalArcRouteBConsumer


open Lean in
run_cmd do
  let env ← getEnv
  let mods : Array Name := #[ `SerrePositivity.AlgebraicGeometry.ArcRouteB.AicProductArc, `SerrePositivity.AlgebraicGeometry.ArcRouteB.AicValuationArc, `SerrePositivity.AlgebraicGeometry.ArcRouteB.ArcCoverCech, `SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeArrowComparison, `SerrePositivity.AlgebraicGeometry.ArcRouteB.BaseChangeComparison, `SerrePositivity.AlgebraicGeometry.ArcRouteB.CoverLaws, `SerrePositivity.AlgebraicGeometry.ArcRouteB.Definitions, `SerrePositivity.AlgebraicGeometry.ArcRouteB.EndpointSections, `SerrePositivity.AlgebraicGeometry.ArcRouteB.FilteredUniversalCech, `SerrePositivity.AlgebraicGeometry.ArcRouteB.FpResiduePoint, `SerrePositivity.AlgebraicGeometry.ArcRouteB.FrobeniusPerfect, `SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalCoefficientPerfect, `SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalGluing, `SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalPoints, `SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalRestrictions, `SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalSpectrum, `SerrePositivity.AlgebraicGeometry.ArcRouteB.IntervalTensorComparison, `SerrePositivity.AlgebraicGeometry.ArcRouteB.LocalExtensions, `SerrePositivity.AlgebraicGeometry.ArcRouteB.ModelUnder, `SerrePositivity.AlgebraicGeometry.ArcRouteB.OverlapCoefficientDetection, `SerrePositivity.AlgebraicGeometry.ArcRouteB.OverlapComplex, `SerrePositivity.AlgebraicGeometry.ArcRouteB.OverlapShortExact, `SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedFpArc, `SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedModelCocone, `SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedModelColimit, `SerrePositivity.AlgebraicGeometry.ArcRouteB.PerfectedModelDiagram, `SerrePositivity.AlgebraicGeometry.ArcRouteB.ProbeComparison, `SerrePositivity.AlgebraicGeometry.ArcRouteB.ProbeTerms, `SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalCech, `SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalOverlap, `SerrePositivity.AlgebraicGeometry.ArcRouteB.UniversalUltraproduct ]
  let decls := env.constants.toList
  let mut total := 0
  for mod in mods do
    unless env.header.modules.any (·.module == mod) do
      throwError "2i ArcRouteB: module not imported: {mod}"
    let mut count : Nat := 0
    for (name, _) in decls do
      let some idx := env.getModuleIdxFor? name | continue
      unless env.header.modules[idx.toNat]!.module == mod do continue
      let axioms ← collectAxioms name
      unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
        throwError "2i ArcRouteB: unexpected axioms in {name}: {axioms}"
      count := count + 1
    if count == 0 then throwError "no declarations audited: {mod}"
    total := total + count
    logInfo m!"{mod}: {count} declarations, standard three axioms only."
  logInfo m!"2i ArcRouteB audit passed: {total} declarations."

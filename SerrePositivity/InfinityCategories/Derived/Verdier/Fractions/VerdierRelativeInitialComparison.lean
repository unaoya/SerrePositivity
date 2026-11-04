module

public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeComparisonPrism
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.RelativeFunctorCoreRestriction
public import SerrePositivity.KST.LocalizingInvariants.CoconeComparisonPrism
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreComparison
public import SerrePositivity.KST.LocalizingInvariants.RelativeSimplexAttachmentHomotopy
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierInitialComparisonRestriction

/-!
概要：構成済みの K 始端全比較を、指定された S 始端全比較へ厳密に合わせる。
方針：証明済み両制限の一致を同じ prism へ移し、元の attachment RLP を実適用する。
規約：両端・全前段・全次辺と指定 S 全比較を、同じ Homotopy の全時刻で保持する。
使われ方：元の第一行亜群化上で全円柱比較を延長する際の K 始端境界。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}
  {r : VerdierFiniteMappingCoconeRecovery h D z S a f}
  {U : VerdierRecoveredQuotientCoconeCylinder r G}

local notation "P" => S.toSSet ⊗ (Δ[1] : SSet)
local notation "J" => join (Δ[n] : SSet) Δ[0]

def VerdierRecoveredInitialComparison.ambientHomotopy
    (c : VerdierRecoveredInitialComparison r U) :
    SSet.Homotopy (r.cylinder.whole ≫ (ihom J).map q.hom) U.initialFamily :=
  spanFunctorEdgeUnflipHomotopy c.edge

lemma VerdierRecoveredInitialComparison.ambientHomotopy_h
    (c : VerdierRecoveredInitialComparison r U) :
    c.ambientHomotopy.h = spanComparisonPrism c.edge.edge :=
  spanFunctorEdgeUnflipHomotopy_h c.edge

def VerdierRecoveredBoundaryComparison.ambientHomotopy
    (b : VerdierRecoveredBoundaryComparison r U) :
    SSet.Homotopy (r.cylinder.homotopy.h ≫ (ihom J).map q.hom) ((S.ι ▷ Δ[1]) ≫ U.whole) :=
  spanFunctorEdgeUnflipHomotopy b.edge

lemma VerdierRecoveredBoundaryComparison.ambientHomotopy_h
    (b : VerdierRecoveredBoundaryComparison r U) :
    b.ambientHomotopy.h = spanComparisonPrism b.edge.edge :=
  spanFunctorEdgeUnflipHomotopy_h b.edge

/-- 指定された全 S 境界比較の始端。二つの実円柱の始端を保持して取り出す。 -/
def VerdierRecoveredBoundaryComparison.initialAmbientHomotopy
    (b : VerdierRecoveredBoundaryComparison r U) :
    SSet.Homotopy (S.ι ≫ (r.cylinder.whole ≫ (ihom J).map q.hom))
      (S.ι ≫ U.initialFamily) := by
  let H := functorHomotopyPrecomp b.ambientHomotopy (SSet.ι₀ : S.toSSet ⟶ P)
  have hF : (SSet.ι₀ : S.toSSet ⟶ P) ≫
      (r.cylinder.homotopy.h ≫ (ihom J).map q.hom) =
      S.ι ≫ (r.cylinder.whole ≫ (ihom J).map q.hom) := by
    rw [← Category.assoc, r.cylinder.homotopy.h₀, Category.assoc]
  have hG : (SSet.ι₀ : S.toSSet ⟶ P) ≫ ((S.ι ▷ Δ[1]) ≫ U.whole) =
      S.ι ≫ U.initialFamily := by
    rw [SSet.ι₀_comp_assoc]
    rfl
  exact { h := H.h, h₀ := H.h₀.trans hF, h₁ := H.h₁.trans hG, rel := H.rel }

lemma VerdierRecoveredBoundaryComparison.initialAmbientHomotopy_h
    (b : VerdierRecoveredBoundaryComparison r U) :
    b.initialAmbientHomotopy.h =
      ((SSet.ι₀ : S.toSSet ⟶ P) ▷ (Δ[1] : SSet.{u})) ≫ spanComparisonPrism b.edge.edge := by
  change ((SSet.ι₀ : S.toSSet ⟶ P) ▷ (Δ[1] : SSet.{u})) ≫ b.ambientHomotopy.h = _
  rw [b.ambientHomotopy_h]

namespace VerdierRecoveredInitialComparison
variable (c : VerdierRecoveredInitialComparison r U) (b : VerdierRecoveredBoundaryComparison r U)

lemma initialAmbient_prefix : b.initialAmbientHomotopy.h ≫
    (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
    (S.ι ▷ (Δ[1] : SSet.{u})) ≫ c.ambientHomotopy.h ≫
      (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj := by
  rw [b.initialAmbientHomotopy_h, c.ambientHomotopy_h]
  simp only [spanComparisonPrism_pre_diagram, spanComparisonPrism_pre_parameter]
  exact congrArg (fun e => spanComparisonPrism (K := S.toSSet)
    (L := (Δ[n] : SSet.{u})) (X := C.obj) e) (c.boundary_prefix_eq b)

lemma initialAmbient_last : b.initialAmbientHomotopy.h ≫
    (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
    (S.ι ▷ (Δ[1] : SSet.{u})) ≫ c.ambientHomotopy.h ≫
      (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj := by
  rw [b.initialAmbientHomotopy_h, c.ambientHomotopy_h]
  simp only [spanComparisonPrism_pre_diagram, spanComparisonPrism_pre_parameter]
  exact congrArg (fun e => spanComparisonPrism (K := S.toSSet)
    (L := join (Δ[0] : SSet.{u}) Δ[0]) (X := C.obj) e) (c.boundary_last_eq b)

lemma initialTarget_inverts (_c : VerdierRecoveredInitialComparison r U) :
    InvertsEdges U.initialFamily Set.univ := by
  have hc := (invertsAllEdges_toKan ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫
    U.coreWhole)).comp (quasicategoryCore ((ihom J).obj C.obj)).ι
  simpa only [VerdierRecoveredQuotientCoconeCylinder.initialFamily,
    Category.assoc, U.coreWhole_ι] using hc

include c in
lemma initialSource_inverts :
    InvertsEdges (r.cylinder.whole ≫ (ihom J).map q.hom) Set.univ :=
  spanFunctorEdgeUnflip_invertsAllEdges c.edge c.isInvertible c.initialTarget_inverts

lemma ambientHomotopy_invertsAllEdges : InvertsEdges c.ambientHomotopy.h Set.univ := by
  let H := spanFunctorEdgeUnflipCoreHomotopy c.edge c.isInvertible c.initialTarget_inverts
  have hc := (invertsAllEdges_toKan H.h).comp (quasicategoryCore ((ihom J).obj C.obj)).ι
  have hh : H.h ≫ (quasicategoryCore ((ihom J).obj C.obj)).ι = spanComparisonPrism c.edge.edge :=
    spanFunctorEdgeUnflipCoreHomotopy_ι c.edge c.isInvertible c.initialTarget_inverts
  rw [hh] at hc
  rw [c.ambientHomotopy_h]
  exact hc

/-- 同じ保存済み K 実全族を、元の strict core 逆像へ戻す。 -/
def relativeFamily (c : VerdierRecoveredInitialComparison r U) :
    K ⟶ (relativeFunctorCore q.hom J : SSet.{u}) :=
  corePreimageLift ((ihom J).map q.hom) r.cylinder.whole c.initialSource_inverts

end VerdierRecoveredInitialComparison

/-- 同じ K 始端比較を指定 S 始端比較へ、両端と両制限を保持して実際に延長する。 -/
private lemma exists_relativeInitialHomotopy
    (c : VerdierRecoveredInitialComparison r U) (b : VerdierRecoveredBoundaryComparison r U) :
    ∃ H : SSet.Homotopy (r.cylinder.whole ≫ (ihom J).map q.hom) U.initialFamily,
      (S.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h = b.initialAmbientHomotopy.h ∧
      H.h ≫ (pre (simplexAttachmentBoundary n).ι).app C.obj =
        c.ambientHomotopy.h ≫ (pre (simplexAttachmentBoundary n).ι).app C.obj ∧
      H.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
        c.ambientHomotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj ∧
      H.h ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
        c.ambientHomotopy.h ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj :=
  exists_relative_simplexAttachmentHomotopy n S.ι c.ambientHomotopy b.initialAmbientHomotopy
    (c.initialAmbient_prefix b) (c.initialAmbient_last b)

/-- 指定 S 比較と両制限を保持し、元の core に入る同じ K 始端全比較。 -/
structure VerdierRelativeInitialComparison
    (c : VerdierRecoveredInitialComparison r U) (b : VerdierRecoveredBoundaryComparison r U) where
  homotopy : SSet.Homotopy (r.cylinder.whole ≫ (ihom J).map q.hom) U.initialFamily
  boundary_eq : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h = b.initialAmbientHomotopy.h
  attachment_eq : homotopy.h ≫ (pre (simplexAttachmentBoundary n).ι).app C.obj =
    c.ambientHomotopy.h ≫ (pre (simplexAttachmentBoundary n).ι).app C.obj
  prefix_eq : homotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
    c.ambientHomotopy.h ≫ (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj
  last_eq : homotopy.h ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
    c.ambientHomotopy.h ≫ (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj
  invertsAllEdges : InvertsEdges homotopy.h Set.univ

/-- 一致を新仮定にせず証明し、元の attachment RLP で指定 S 始端比較へ実際に合わせる。 -/
lemma exists_verdierRelativeInitialComparison
    (c : VerdierRecoveredInitialComparison r U) (b : VerdierRecoveredBoundaryComparison r U) :
    Nonempty (VerdierRelativeInitialComparison c b) := by
  obtain ⟨H, hS, hA, hP, hN⟩ := exists_relativeInitialHomotopy c b
  let p := (pre (simplexAttachmentBoundary n).ι).app C.obj
  have hff := (isQCatEquivalence_of_trivialKanFibration p).isFullyFaithful
  have hp : InvertsEdges (H.h ≫ p) Set.univ := by
    rw [hA]
    exact c.ambientHomotopy_invertsAllEdges.comp p
  have hi : InvertsEdges H.h Set.univ := by
    intro e he
    exact hff.reflects_isInvertibleEdge ((edgeOfSimplex e).map ((truncation 2).map H.h)) (hp he)
  exact ⟨⟨H, hS, hA, hP, hN, hi⟩⟩

namespace VerdierRelativeInitialComparison
variable {c : VerdierRecoveredInitialComparison r U} {b : VerdierRecoveredBoundaryComparison r U}
  (d : VerdierRelativeInitialComparison c b)

def corePrism : K ⊗ (Δ[1] : SSet.{u}) ⟶
    (quasicategoryCore ((ihom J).obj C.obj) : SSet.{u}) :=
  allEdgesCoreLift d.homotopy.h d.invertsAllEdges

lemma corePrism_ι : d.corePrism ≫ (quasicategoryCore ((ihom J).obj C.obj)).ι = d.homotopy.h :=
  allEdgesCoreLift_ι _ _

/-- 同じ調整済み実比較を、元の core 内の両端固定 Homotopy として回収する。 -/
def coreHomotopy : SSet.Homotopy (c.relativeFamily ≫ relativeFunctorCoreQuotient q.hom J)
    ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ U.coreWhole) where
  h := d.corePrism
  h₀ := by
    apply (cancel_mono (quasicategoryCore ((ihom J).obj C.obj)).ι).mp
    rw [Category.assoc, d.corePrism_ι, d.homotopy.h₀]
    rfl
  h₁ := by
    apply (cancel_mono (quasicategoryCore ((ihom J).obj C.obj)).ι).mp
    rw [Category.assoc, d.corePrism_ι, d.homotopy.h₁]
    rfl
  rel := by
    apply SSet.hom_ext
    intro m
    apply ConcreteCategory.hom_ext
    intro v
    exact False.elim v.1.property

/-- 指定された同じ S 全境界比較の始端を、core 内でも全写像として厳密保持する。 -/
lemma boundary_core_eq : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ d.corePrism =
    ((SSet.ι₀ : S.toSSet ⟶ P) ▷ (Δ[1] : SSet.{u})) ≫ b.coreHomotopy.h := by
  apply (cancel_mono (quasicategoryCore ((ihom J).obj C.obj)).ι).mp
  simp only [Category.assoc, d.corePrism_ι, b.coreHomotopy_ι]
  rw [d.boundary_eq, b.initialAmbientHomotopy_h]
  rfl

def iso : FunctorIso (r.cylinder.whole ≫ (ihom J).map q.hom) U.initialFamily :=
  VertexIso.map (functorIsoOfSimplicialHomotopy d.coreHomotopy)
    ((ihom K).map (quasicategoryCore ((ihom J).obj C.obj)).ι)

end VerdierRelativeInitialComparison

end SerrePositivity.KST.LocalizingInvariants

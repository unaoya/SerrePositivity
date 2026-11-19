module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.CoconeComparisonPrism
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeFunctorCoreRestriction
public import SerrePositivity.KST.LocalizingInvariants.CoconeComparisonPrism
public import SerrePositivity.KST.LocalizingInvariants.CoconeFamilyCoreComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.RelativeSimplexAttachmentHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierInitialComparisonRestriction

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison
end SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison
namespace SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison
end SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison
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
  {r : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f}
  {U : VerdierRecoveredQuotientCoconeCylinder r G}

local notation "P" => S.toSSet ⊗ (Δ[1] : SSet)
local notation "J" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet) Δ[0]

def VerdierRecoveredInitialComparison.ambientHomotopy
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) :
    SSet.Homotopy (r.cylinder.whole ≫ (ihom J).map q.hom) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily U) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorEdgeUnflipHomotopy c.edge

lemma VerdierRecoveredInitialComparison.ambientHomotopy_h
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) :
    c.ambientHomotopy.h = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism c.edge.edge :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorEdgeUnflipHomotopy_h c.edge

def VerdierRecoveredBoundaryComparison.ambientHomotopy
    (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) :
    SSet.Homotopy (r.cylinder.homotopy.h ≫ (ihom J).map q.hom) ((S.ι ▷ Δ[1]) ≫ U.whole) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorEdgeUnflipHomotopy b.edge

lemma VerdierRecoveredBoundaryComparison.ambientHomotopy_h
    (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) :
    b.ambientHomotopy.h = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism b.edge.edge :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanFunctorEdgeUnflipHomotopy_h b.edge

/-- 指定された全 S 境界比較の始端。二つの実円柱の始端を保持して取り出す。 -/
def VerdierRecoveredBoundaryComparison.initialAmbientHomotopy
    (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) :
    SSet.Homotopy (S.ι ≫ (r.cylinder.whole ≫ (ihom J).map q.hom))
      (S.ι ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily U)) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp b.ambientHomotopy (SSet.ι₀ : S.toSSet ⟶ P)
  have hF : (SSet.ι₀ : S.toSSet ⟶ P) ≫
      (r.cylinder.homotopy.h ≫ (ihom J).map q.hom) =
      S.ι ≫ (r.cylinder.whole ≫ (ihom J).map q.hom) := by
    rw [← Category.assoc, r.cylinder.homotopy.h₀, Category.assoc]
  have hG : (SSet.ι₀ : S.toSSet ⟶ P) ≫ ((S.ι ▷ Δ[1]) ≫ U.whole) =
      S.ι ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily U) := by
    rw [SSet.ι₀_comp_assoc]
    rfl
  exact { h := H.h, h₀ := H.h₀.trans hF, h₁ := H.h₁.trans hG, rel := H.rel }

lemma VerdierRecoveredBoundaryComparison.initialAmbientHomotopy_h
    (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) :
    b.initialAmbientHomotopy.h =
      ((SSet.ι₀ : S.toSSet ⟶ P) ▷ (Δ[1] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism b.edge.edge := by
  change ((SSet.ι₀ : S.toSSet ⟶ P) ▷ (Δ[1] : SSet.{u})) ≫ b.ambientHomotopy.h = _
  rw [b.ambientHomotopy_h]

namespace VerdierRecoveredInitialComparison

variable (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U)

lemma initialAmbient_prefix : b.initialAmbientHomotopy.h ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
    (S.ι ▷ (Δ[1] : SSet.{u})) ≫ c.ambientHomotopy.h ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj := by
  rw [b.initialAmbientHomotopy_h, c.ambientHomotopy_h]
  simp only [spanComparisonPrism_pre_diagram, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism_pre_parameter]
  exact congrArg (fun e => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism (K := S.toSSet)
    (L := (Δ[n] : SSet.{u})) (X := C.obj) e) (c.boundary_prefix_eq b)

lemma initialAmbient_last : b.initialAmbientHomotopy.h ≫
    (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
    (S.ι ▷ (Δ[1] : SSet.{u})) ≫ c.ambientHomotopy.h ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj := by
  rw [b.initialAmbientHomotopy_h, c.ambientHomotopy_h]
  simp only [spanComparisonPrism_pre_diagram, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism_pre_parameter]
  exact congrArg (fun e => _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism (K := S.toSSet)
    (L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[0]) (X := C.obj) e) (c.boundary_last_eq b)

lemma initialTarget_inverts (_c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily U) Set.univ := by
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertsAllEdges_toKan ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫
    U.coreWhole)).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily,
    Category.assoc, U.coreWhole_ι] using hc

include c in
lemma initialSource_inverts :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (r.cylinder.whole ≫ (ihom J).map q.hom) Set.univ :=
  spanFunctorEdgeUnflip_invertsAllEdges c.edge c.isInvertible c.initialTarget_inverts

lemma ambientHomotopy_invertsAllEdges : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges c.ambientHomotopy.h Set.univ := by
  let H := spanFunctorEdgeUnflipCoreHomotopy c.edge c.isInvertible c.initialTarget_inverts
  have hc := (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.invertsAllEdges_toKan H.h).comp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι
  have hh : H.h ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι = _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanComparisonPrism c.edge.edge :=
    spanFunctorEdgeUnflipCoreHomotopy_ι c.edge c.isInvertible c.initialTarget_inverts
  rw [hh] at hc
  rw [c.ambientHomotopy_h]
  exact hc

/-- 同じ保存済み K 実全族を、元の strict core 逆像へ戻す。 -/
def relativeFamily (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) :
    K ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q.hom J : SSet.{u}) :=
  corePreimageLift ((ihom J).map q.hom) r.cylinder.whole c.initialSource_inverts

end VerdierRecoveredInitialComparison

/-- 同じ K 始端比較を指定 S 始端比較へ、両端と両制限を保持して実際に延長する。 -/
private lemma exists_relativeInitialHomotopy
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) :
    ∃ H : SSet.Homotopy (r.cylinder.whole ≫ (ihom J).map q.hom) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily U),
      (S.ι ▷ (Δ[1] : SSet.{u})) ≫ H.h = b.initialAmbientHomotopy.h ∧
      H.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C.obj =
        c.ambientHomotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C.obj ∧
      H.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
        c.ambientHomotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj ∧
      H.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
        c.ambientHomotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj :=
  exists_relative_simplexAttachmentHomotopy n S.ι c.ambientHomotopy b.initialAmbientHomotopy
    (c.initialAmbient_prefix b) (c.initialAmbient_last b)

/-- 指定 S 比較と両制限を保持し、元の core に入る同じ K 始端全比較。 -/
structure VerdierRelativeInitialComparison
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) where
  homotopy : SSet.Homotopy (r.cylinder.whole ≫ (ihom J).map q.hom) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily U)
  boundary_eq : (S.ι ▷ (Δ[1] : SSet.{u})) ≫ homotopy.h = b.initialAmbientHomotopy.h
  attachment_eq : homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C.obj =
    c.ambientHomotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C.obj
  prefix_eq : homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
    c.ambientHomotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj
  last_eq : homotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
    c.ambientHomotopy.h ≫ (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj
  invertsAllEdges : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges homotopy.h Set.univ

/-- 一致を新仮定にせず証明し、元の attachment RLP で指定 S 始端比較へ実際に合わせる。 -/
lemma exists_verdierRelativeInitialComparison
    (c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U) (b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison c b) := by
  obtain ⟨H, hS, hA, hP, hN⟩ := exists_relativeInitialHomotopy c b
  let p := (pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C.obj
  have hff := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration p).isFullyFaithful
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges (H.h ≫ p) Set.univ := by
    rw [hA]
    exact c.ambientHomotopy_invertsAllEdges.comp p
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges H.h Set.univ := by
    intro e he
    exact hff.reflects_isInvertibleEdge ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex e).map ((truncation 2).map H.h)) (hp he)
  exact ⟨⟨H, hS, hA, hP, hN, hi⟩⟩

namespace VerdierRelativeInitialComparison

variable {c : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison r U} {b : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison r U}
  (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison c b)

def corePrism : K ⊗ (Δ[1] : SSet.{u}) ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj) : SSet.{u}) :=
  allEdgesCoreLift d.homotopy.h d.invertsAllEdges

lemma corePrism_ι : d.corePrism ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι = d.homotopy.h :=
  allEdgesCoreLift_ι _ _

/-- 同じ調整済み実比較を、元の core 内の両端固定 Homotopy として回収する。 -/
def coreHomotopy : SSet.Homotopy (c.relativeFamily ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q.hom J)
    ((SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ U.coreWhole) where
  h := d.corePrism
  h₀ := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι).mp
    rw [Category.assoc, d.corePrism_ι, d.homotopy.h₀]
    rfl
  h₁ := by
    apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι).mp
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
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι).mp
  simp only [Category.assoc, d.corePrism_ι, b.coreHomotopy_ι]
  rw [d.boundary_eq, b.initialAmbientHomotopy_h]
  rfl

def iso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (r.cylinder.whole ≫ (ihom J).map q.hom) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily U) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy d.coreHomotopy)
    ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom J).obj C.obj)).ι)

end VerdierRelativeInitialComparison

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierRelativeInitialComparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.exists_verdierRelativeInitialComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.ambientHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.ambientHomotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.ambientHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.ambientHomotopy_h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.ambientHomotopy_h

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy_h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy_h

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.ambientHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.ambientHomotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.ambientHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.ambientHomotopy_h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.ambientHomotopy_h

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.ambientHomotopy_invertsAllEdges := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.ambientHomotopy_invertsAllEdges

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.initialAmbient_last := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.initialAmbient_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.initialAmbient_prefix := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.initialAmbient_prefix

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.initialSource_inverts := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.initialSource_inverts

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.initialTarget_inverts := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.initialTarget_inverts

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.relativeFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredInitialComparison.relativeFamily := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredInitialComparison.relativeFamily

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison._sizeOf_inst

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.attachment_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.attachment_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.boundary_core_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.boundary_core_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.boundary_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.boundary_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.casesOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.coreHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.coreHomotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.coreHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.corePrism (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.corePrism := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.corePrism

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.corePrism_ι := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.corePrism_ι

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.ctorIdx := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.homotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.homotopy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.homotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.invertsAllEdges := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.invertsAllEdges

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.iso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.iso := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.iso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.last_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.last_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.mk := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.noConfusionType := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.noConfusionType

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.prefix_eq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.prefix_eq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.rec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.recOn := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.recOn

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy._proof_5 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRecoveredBoundaryComparison.initialAmbientHomotopy._proof_5

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.coreHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.coreHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.coreHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.coreHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.coreHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.coreHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.iso._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.iso._proof_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.mk.inj := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.mk.injEq := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRelativeInitialComparison.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierRelativeInitialComparison.mk.sizeOf_spec

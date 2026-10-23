module

public import SerrePositivity.InfinityCategories.F1.TwistedArrow.SourceInitial
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.F1.Fibrations.PullbackTransport
public import SerrePositivity.InfinityCategories.F1B.RightFibrationInitialFiber

/-!
概要：始点を固定した全 twisted arrow と元の right fibration の元の圏を比較する。
方針：始対象上の fiber の包含が弱同値である既存の一般定理を適用する。
規約：固定した同じ始対象と、元の射影の fiber を使う。
使われ方：恒等点上の評価の同値を、同じ始点を持つ全族の評価へ広げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {E B : SSet.{u}} (p : E ⟶ B) [RightFibration p] (b : B _⦋0⦌)

/-- 同じ始点を持つ全 twisted arrow と、その終点上の元の全空間の族。 -/
def twistedSourceElements : SSet.{u} := pullback p (twistedArrowSourceProjection b)

/-- 始点固定の twisted arrow の全空間への射影。 -/
def twistedSourceElementsProjection : twistedSourceElements p b ⟶ twistedArrowSource b :=
  pullback.snd _ _

instance twistedSourceElementsProjection_rightFibration :
    RightFibration (twistedSourceElementsProjection p b) :=
  ⟨rightFibrations.pullback_snd _ _ (RightFibration.mem (p := p))⟩

/-- 同じ恒等点上の fiber は、元の射影の指定 fiber と厳密に同型。 -/
def twistedSourceElementsIdentityFiberIso [Quasicategory B] :
    vertexFiber (twistedSourceElementsProjection p b) (twistedArrowSourceIdentity b) ≅
      vertexFiber p b :=
  vertexFiberPullbackIso p (twistedArrowSourceProjection b) (twistedArrowSourceIdentity b) ≪≫
    eqToIso (congrArg (vertexFiber p) (twistedArrowSourceIdentity_projection b))

/-- 元の同じ fiber を、同じ始点を持つ全族へ含める。 -/
def twistedSourceElementsIdentityInclusion [Quasicategory B] :
    vertexFiber p b ⟶ twistedSourceElements p b :=
  (twistedSourceElementsIdentityFiberIso p b).inv ≫
    vertexFiberι (twistedSourceElementsProjection p b) (twistedArrowSourceIdentity b)

omit [RightFibration p] in
/-- 恒等点の包含の全空間成分は、元の同じ fiber 包含。 -/
lemma twistedSourceElementsIdentityInclusion_fst [Quasicategory B] :
    twistedSourceElementsIdentityInclusion p b ≫ pullback.fst p (twistedArrowSourceProjection b) =
      vertexFiberι p b := by
  have ht (a c : B _⦋0⦌) (h : a = c) :
      (eqToIso (congrArg (vertexFiber p) h)).inv ≫ vertexFiberι p a = vertexFiberι p c := by
    subst c
    simp only [eqToIso_refl, Iso.refl_inv, Category.id_comp]
  change (eqToIso (congrArg (vertexFiber p) (twistedArrowSourceIdentity_projection b))).inv ≫
    (vertexFiberPullbackIso p (twistedArrowSourceProjection b) (twistedArrowSourceIdentity b)).inv ≫
    vertexFiberι _ _ ≫ pullback.fst _ _ = _
  rw [vertexFiberPullbackIso_inv_ι_fst]
  exact ht _ _ (twistedArrowSourceIdentity_projection b)

omit [RightFibration p] in
/-- 恒等点の包含の始点固定の底成分は、指定した同じ恒等点に定値。 -/
lemma twistedSourceElementsIdentityInclusion_snd [Quasicategory B] :
    twistedSourceElementsIdentityInclusion p b ≫ pullback.snd p (twistedArrowSourceProjection b) =
      SSet.const (twistedArrowSourceIdentity b) := by
  change (twistedSourceElementsIdentityFiberIso p b).inv ≫
    vertexFiberι (twistedSourceElementsProjection p b) (twistedArrowSourceIdentity b) ≫
      twistedSourceElementsProjection p b = _
  rw [vertexFiberι_comp, SSet.comp_const]

/-- 指定した恒等点の fiber は、同じ始点を持つ全族の弱ホモトピー型を保つ。 -/
lemma twistedSourceElementsIdentityInclusion_isWeakHomotopyEquivalence [Quasicategory B] :
    IsWeakHomotopyEquivalence (twistedSourceElementsIdentityInclusion p b) := by
  have h := isPrecompositionEquivalence_of_iso (twistedSourceElementsIdentityFiberIso p b).symm
  exact h.isWeakHomotopyEquivalence.comp
    (rightFibration_initialFiber_isWeakHomotopyEquivalence (twistedSourceElementsProjection p b)
      (twistedArrowSourceIdentity b) (twistedArrowSourceIdentity_isInitialVertex b))

end SerrePositivity.InfinityCategories.F2.Ind

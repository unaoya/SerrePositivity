module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningLimitVertexComputations
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftPullbackLimitTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.OverEquivalenceLimitRelativeIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitVertexIsoRestriction

/-!
概要：指定分類の復元spanによる極限比較を、同じ実射による比較で計算する。
方針：既存の相対同型不変性と、元の制限錐の比較の合成を使う。
規約：HTT §1.2.13、Kerodon §7.1（Tag 02H1）の極限比較の法則。
使われ方：R04.4。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance nativeArrow_pullbackLeft {E B K : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (f : K ⟶ B) : LeftFibration (pullback.snd p f) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := p))⟩

local instance actualArrow_pullbackQuasicategory {E B K : SSet.{u}} [Quasicategory K]
    (p : E ⟶ B) [LeftFibration p] (f : K ⟶ B) : Quasicategory (pullback p f) :=
  quasicategory_of_innerFibration (pullback.snd p f)

private lemma limitVertexIso_restriction_comp {A B C X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory X]
    (a : A ⟶ B) (b : B ⟶ C) (ea : IsQCatEquivalence a) (eb : IsQCatEquivalence b)
    (F : A ⟶ X) (G : B ⟶ X) (H : C ⟶ X)
    (ha : a ≫ G = F) (hb : b ≫ H = G)
    (c : JoinCone F) (d : JoinCone G) (e : JoinCone H)
    (hc : IsLimitCone c) (hd : IsLimitCone d) (he : IsLimitCone e) :
    let hab : (a ≫ b) ≫ H = F := by rw [Category.assoc, hb, ha]
    let da := (restrictJoinCone d a).cast ha
    let eb₀ := (restrictJoinCone e b).cast hb
    let eab := (restrictJoinCone e (a ≫ b)).cast hab
    ∀ (hda : IsLimitCone da) (heb : IsLimitCone eb₀) (heab : IsLimitCone eab),
    ((limitVertexIso c da hc hda).hom ≫
        eqToHom (congrArg HomotopyCategory.mk
          ((JoinCone.vertex_cast _ ha).trans (restrictJoinCone_vertex d a)))) ≫
      ((limitVertexIso d eb₀ hd heb).hom ≫
        eqToHom (congrArg HomotopyCategory.mk
          ((JoinCone.vertex_cast _ hb).trans (restrictJoinCone_vertex e b)))) =
    (limitVertexIso c eab hc heab).hom ≫
        eqToHom (congrArg HomotopyCategory.mk
          ((JoinCone.vertex_cast _ hab).trans (restrictJoinCone_vertex e (a ≫ b)))) := by
  subst F
  subst G
  dsimp only
  have hAs : a ≫ b ≫ H = (a ≫ b) ≫ H := (Category.assoc a b H).symm
  let eb₀ := restrictJoinCone e b
  let eba := restrictJoinCone eb₀ a
  have ebaEq : eba = (restrictJoinCone e (a ≫ b)).cast hAs.symm := by
    apply Subtype.ext
    change joinMap (𝟙 (Δ[0] : SSet.{u})) a ≫
      (joinMap (𝟙 (Δ[0] : SSet.{u})) b ≫ e.val) =
      joinMap (𝟙 (Δ[0] : SSet.{u})) (a ≫ b) ≫ e.val
    rw [← Category.assoc, ← joinMap_comp, Category.id_comp]
  intro hda heb heab
  have heba : IsLimitCone eba := (isLimitCone_iff_restrict_equivalentShape a ea eb₀).mp heb
  have hm := limitVertexIso_restrict_hom a d eb₀ hd heb hda heba
  simp only [JoinCone.vertex_cast, eqToHom_refl, Category.id_comp, Category.comp_id] at hm ⊢
  change (limitVertexIso c (restrictJoinCone d a) hc hda).hom ≫
      (limitVertexIso d eb₀ hd heb).hom =
    (limitVertexIso c ((restrictJoinCone e (a ≫ b)).cast hAs.symm) hc heab).hom
  rw [hm, limitVertexIso_hom_comp]
  have aligned (x y : JoinCone (a ≫ b ≫ H)) (h : x = y)
      (hx : IsLimitCone x) (hy : IsLimitCone y) :
      Arrow.mk (limitVertexIso c x hc hx).hom = Arrow.mk (limitVertexIso c y hc hy).hom := by
    subst y
    rfl
  exact Arrow.mk_injective _ _ (aligned _ _ ebaEq heba heab)

private lemma limitVertexIso_over_comp {A B C K X : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory X]
    (a : A ⟶ B) (b : B ⟶ C) (ea : IsQCatEquivalence a) (eb : IsQCatEquivalence b)
    {p : A ⟶ K} {q : B ⟶ K} {r : C ⟶ K} (ha : a ≫ q = p) (hb : b ≫ r = q)
    (O : K ⟶ X) (c : JoinCone (p ≫ O)) (d : JoinCone (q ≫ O)) (e : JoinCone (r ≫ O))
    (hc : IsLimitCone c) (hd : IsLimitCone d) (he : IsLimitCone e) :
    let hab : (a ≫ b) ≫ r = p := by rw [Category.assoc, hb, ha]
    (limitVertexIsoOfOverEquivalence a ea ha O c d hc hd).hom ≫
      (limitVertexIsoOfOverEquivalence b eb hb O d e hd he).hom =
      (limitVertexIsoOfOverEquivalence (a ≫ b) (ea.comp eb) hab O c e hc he).hom := by
  intro hab
  have hA : a ≫ (q ≫ O) = p ≫ O := by rw [← Category.assoc, ha]
  have hB : b ≫ (r ≫ O) = q ≫ O := by rw [← Category.assoc, hb]
  have hAB : (a ≫ b) ≫ (r ≫ O) = p ≫ O := by rw [← Category.assoc, hab]
  have hda := ((isLimitCone_iff_restrict_equivalentShape a ea d).mp hd).cast hA
  have heb := ((isLimitCone_iff_restrict_equivalentShape b eb e).mp he).cast hB
  have heab := ((isLimitCone_iff_restrict_equivalentShape (a ≫ b) (ea.comp eb) e).mp he).cast hAB
  rw [limitVertexIsoOfOverEquivalence_hom_restriction p q a ha ea O c d hc hd hda,
    limitVertexIsoOfOverEquivalence_hom_restriction q r b hb eb O d e hd he heb,
    limitVertexIsoOfOverEquivalence_hom_restriction p r (a ≫ b) hab (ea.comp eb) O c e hc he heab]
  exact limitVertexIso_restriction_comp a b ea eb _ _ _ hA hB c d e hc hd he hda heb heab

/-- 同じ相対比較を与える実射は、指定復元spanと同じ極限頂点射を与える。 -/
@[cite HTT "1.2.13" (partial := special)
  "指定された引き戻しの分類図式と実射による極限比較の照合。"]
lemma leftPullback_limitVertexIso_eq_actualArrow :
∀ {E B K : SSet.{u}} [Quasicategory B] [Quasicategory K]
 (p : E ⟶ B) [LeftFibration p]
 (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
 {f g : K ⟶ B} (e : FunctorIso f g),
let pf := pullback.snd p f
let pg := pullback.snd p g
let q := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram pg)
let z := leftStraighteningInfinityReconstruction pf ≫
  smallLeftUnstraighteningComparisonOfFunctorIso (leftPullbackClassificationIso p e)
∀ (a : pullback p f ⟶ pullback p g) (ha : a ≫ pg = pf)
 (ea : IsQCatEquivalence a)
 (h₀ : z ≫ q = pf) (h₁ : (a ≫ leftStraighteningInfinityReconstruction pg) ≫ q = pf)
 (h : VertexIso (relativeFunctorVertex q pf z h₀)
   (relativeFunctorVertex q pf (a ≫ leftStraighteningInfinityReconstruction pg) h₁))
 {X : SSet.{u}} [Quasicategory X] (O : K ⟶ X)
 (c : JoinCone (pf ≫ O)) (d : JoinCone (pg ≫ O))
 (hc : IsLimitCone c) (hd : IsLimitCone d),
 (limitVertexIsoOfLeftStraighteningIso pf pg (leftPullbackClassificationIso p e) O c d hc hd).hom =
 (limitVertexIsoOfOverEquivalence a ea ha O c d hc hd).hom := by
  intro E B K hB hK p hp R f g e
  dsimp only
  intro a ha ea h₀ h₁ h X hX O c d hc hd
  let pf := pullback.snd p f
  let pg := pullback.snd p g
  letI : Quasicategory (pullback p f) := quasicategory_of_innerFibration pf
  letI : Quasicategory (pullback p g) := quasicategory_of_innerFibration pg
  let ν := leftPullbackClassificationIso p e
  let sF := leftStraighteningInfinityReconstruction pf
  let sG := leftStraighteningInfinityReconstruction pg
  let m := smallLeftUnstraighteningComparisonOfFunctorIso ν
  let qF := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram pf)
  let qG := smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram pg)
  let hsF := leftStraighteningInfinityReconstruction_projection pf
  let hsG := leftStraighteningInfinityReconstruction_projection pg
  let hm := smallLeftUnstraighteningComparisonOfFunctorIso_projection ν
  let esF := (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence pf).isQCatEquivalence
  let esG := (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence pg).isQCatEquivalence
  let em := (smallLeftUnstraighteningComparisonOfFunctorIso_isPrecompositionEquivalence ν).isQCatEquivalence
  have hF : HasLimit (qF ≫ O) := by
    apply (hasLimit_iff_equivalentRestriction sF esF _).mpr
    change HasLimit (sF ≫ (qF ≫ O))
    have hw : sF ≫ qF = pf := hsF
    rw [← Category.assoc, hw]
    exact ⟨c, hc⟩
  have hG : HasLimit (qG ≫ O) := by
    apply (hasLimit_iff_equivalentRestriction sG esG _).mpr
    change HasLimit (sG ≫ (qG ≫ O))
    have hw : sG ≫ qG = pg := hsG
    rw [← Category.assoc, hw]
    exact ⟨d, hd⟩
  obtain ⟨s, hs⟩ := hF
  obtain ⟨t, ht⟩ := hG
  let i := limitVertexIsoOfOverEquivalence sG esG hsG O d t hd ht
  have e₀ := limitVertexIso_over_comp sF m esF em hsF hm O c s t hc hs ht
  have e₁ := limitVertexIso_over_comp a sG ea esG ha hsG O c d t hc hd ht
  have er := limitVertexIsoOfOverEquivalence_hom_eq_of_relativeIso pf qG (sF ≫ m) (a ≫ sG)
    h₀ h₁ h (esF.comp em) (ea.comp esG) O c t hc ht
  rw [limitVertexIsoOfLeftStraighteningIso_eq_middle pf pg ν O c d hc hd s t hs ht]
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, e₀, er, ← e₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

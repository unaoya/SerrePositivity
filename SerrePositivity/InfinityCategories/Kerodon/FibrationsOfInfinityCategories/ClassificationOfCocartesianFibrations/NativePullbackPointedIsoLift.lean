module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationFunctorIsoLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NerveStraighteningRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseMorphismUp
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-!
概要：元の表現の二つの底変換の間に、指定した底の同型を被覆するpointed同型を作る。
方針：既存の同型持ち上げをU.mapした第一射影に適用し、元の引き戻しと完全忠実性で射を戻す。
規約：HTT §3.3.2・2.1.1.6、Kerodon Remark 5.6.2.18（Tag 0271）の既存構成の照合。
使われ方：R04-NP。元の指定e、元の表現、元の二つの底変換のpointedMapを保持する。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

private lemma transport_postcomp_heq {A X Y : SSet.{u}}
    {f g f' g' : A ⟶ X} (i : FunctorIso f g) (hf : f = f') (hg : g = g')
    (p : X ⟶ Y) : HEq ((functorIsoOfEq i hf hg).postcomp p) (i.postcomp p) := by
  subst f' g'
  rfl

private lemma postcomp_map_heq {A X Y : SSet.{u}} {f g : A ⟶ X}
    (i : FunctorIso f g) {p q : X ⟶ Y} (h : p = q) :
    HEq (i.postcomp p) (i.postcomp q) := by cases h; rfl

/-- 同じ持ち上げの全空間側とpointed側の指定像を同時に保持する。 -/
@[cite HTT "3.3.2" (partial := special) "同じ既存の持ち上げの両射影を保持する計算法則。"]
lemma exists_nativePullbackPointedIsoLiftData :
∀ {E B K : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    {f g : K ⟶ B} (e : FunctorIso f g),
    ∃ (a : pullback p f ⟶ pullback p g)
      (ha : a ≫ pullback.snd p g = pullback.snd p f)
      (L : FunctorIso
        ((SSet.uliftFunctor.{u + 1, u}).map (pullback.fst p f))
        ((SSet.uliftFunctor.{u + 1, u}).map (a ≫ pullback.fst p g)))
      (P : FunctorIso (R.nativeRestrict f).pointedMap
        ((SSet.uliftFunctor.{u + 1, u}).map a ≫ (R.nativeRestrict g).pointedMap)),
      HEq (L.postcomp ((SSet.uliftFunctor.{u + 1, u}).map p))
        ((functorIso_ulift.{u, u + 1} e).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (pullback.snd p f))) ∧
      HEq (P.postcomp pointedSpaceProjection)
        (((functorIso_ulift.{u, u + 1} e).postcomp R.diagram).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (pullback.snd p f))) := by
  intro E B K hB p hp R f g e
  let U := SSet.uliftFunctor.{u + 1, u}
  letI : Quasicategory E := quasicategory_of_innerFibration p
  let eU := functorIso_ulift.{u, u + 1} e
  let π := U.map (pullback.snd p f)
  have hc : U.map (pullback.fst p f) ≫ U.map p = π ≫ U.map f := by
    rw [← U.map_comp, ← U.map_comp, pullback.condition]
  let e₀ : FunctorIso (U.map (pullback.fst p f) ≫ U.map p) (π ≫ U.map g) :=
    functorIsoOfEq (eU.precomp π) hc.symm rfl
  obtain ⟨l, hl, i, hi⟩ := exists_leftFibration_functorIso_lift (U.map p)
    (U.map (pullback.fst p f)) e₀
  let sq := ulift_isPullback p g
  let aU := sq.lift l π hl
  let a := U.preimage aU
  have hUa : U.map a = aU := U.map_preimage aU
  have ha : a ≫ pullback.snd p g = pullback.snd p f := by
    apply U.map_injective
    rw [U.map_comp, hUa]
    exact sq.lift_snd _ _ _
  have had : U.map (a ≫ pullback.fst p g) = l := by
    rw [U.map_comp, hUa]
    exact sq.lift_fst _ _ _
  have htarget : l ≫ R.pointedMap = U.map a ≫ (R.nativeRestrict g).pointedMap := by
    rw [← had, U.map_comp, Category.assoc, R.nativeRestrict_pointedMap]
  let P : FunctorIso (R.nativeRestrict f).pointedMap
      (U.map a ≫ (R.nativeRestrict g).pointedMap) :=
    functorIsoOfEq (i.postcomp R.pointedMap) (R.nativeRestrict_pointedMap f).symm htarget
  let L : FunctorIso (U.map (pullback.fst p f)) (U.map (a ≫ pullback.fst p g)) :=
    functorIsoOfEq i rfl had.symm
  have hL : HEq (L.postcomp (U.map p)) (eU.precomp π) :=
    (transport_postcomp_heq i rfl had.symm (U.map p)).trans
      ((functorIsoOfEq_heq (i.postcomp (U.map p)) rfl hl).symm.trans
        ((heq_of_eq hi).trans (functorIsoOfEq_heq (eU.precomp π) hc.symm rfl)))
  refine ⟨a, ha, L, P, hL, ?_⟩
  have h₁ : HEq (P.postcomp pointedSpaceProjection)
      ((i.postcomp R.pointedMap).postcomp pointedSpaceProjection) :=
    transport_postcomp_heq _ _ _ _
  have h₂ := postcomp_map_heq i R.pointedMap_projection
  have h₃ : HEq ((i.postcomp (U.map p)).postcomp R.diagram) (e₀.postcomp R.diagram) :=
    (transport_postcomp_heq (i.postcomp (U.map p)) rfl hl R.diagram).symm.trans
      (heq_of_eq (congrArg (fun v => FunctorIso.postcomp v R.diagram) hi))
  have h₄ : HEq (e₀.postcomp R.diagram) ((eU.precomp π).postcomp R.diagram) :=
    transport_postcomp_heq _ _ _ _
  exact h₁.trans ((heq_of_eq (functorIso_postcomp_postcomp i R.pointedMap pointedSpaceProjection)).trans
    (h₂.trans ((heq_of_eq (functorIso_postcomp_postcomp i (U.map p) R.diagram).symm).trans
      (h₃.trans (h₄.trans (heq_of_eq (functorIso_precomp_postcomp eU π R.diagram)))))))

/-- 元の底の同型の像を保ち、二つのnativeな底変換のpointedMapを比較する。 -/
@[cite HTT "3.3.2" (partial := special) "元の同型の持ち上げと既存の引き戻しの普遍性の照合。"]
lemma exists_nativePullbackPointedIsoLift :
∀ {E B K : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    {f g : K ⟶ B} (e : FunctorIso f g),
    ∃ (a : pullback p f ⟶ pullback p g)
      (ha : a ≫ pullback.snd p g = pullback.snd p f)
      (P : FunctorIso (R.nativeRestrict f).pointedMap
        ((SSet.uliftFunctor.{u + 1, u}).map a ≫ (R.nativeRestrict g).pointedMap)),
      HEq (P.postcomp pointedSpaceProjection)
        (((functorIso_ulift.{u, u + 1} e).postcomp R.diagram).precomp
          ((SSet.uliftFunctor.{u + 1, u}).map (pullback.snd p f))) := by
  intro E B K hB p hp R f g e
  obtain ⟨a, ha, L, P, hL, hP⟩ := exists_nativePullbackPointedIsoLiftData p R e
  exact ⟨a, ha, P, hP⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

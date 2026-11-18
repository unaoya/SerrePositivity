module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.NativePullbackPointedIsoLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportRepresentationArrowPointedIso
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallTransportRepresentationArrowPrism

/-!
概要：指定底変換の持ち上げと元のunstraighteningの作用を、同じ局所形状の射aで比較する。
方針：R04-NPの同じpointed同型から元の指定分類辺のprismを取り、R04-PRを適用する。
規約：HTT §3.3.2、Kerodon Remark 5.6.2.18（Tag 0271）の既存構成の照合。
  同じaに対する全空間の指定像と、元の小さい相対写像空間内の比較を同時に保持する。
使われ方：R04の元の復元spanと指定余単位の比較への接続。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

local instance pullbackArrowComparison_leftFibration {E B K : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (f : K ⟶ B) : LeftFibration (pullback.snd p f) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := p))⟩

/-- 元の底の同型の同じ持ち上げは、指定した分類図式の作用を小さい相対写像空間で回収する。 -/
@[cite HTT "3.3.2" (partial := special) "既存の同じpointed prismの比較とnative底変換の接続。"]
lemma exists_nativePullbackRepresentationArrowComparison :
∀ {E B K : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))
    {f g : K ⟶ B} (e : FunctorIso f g),
    let U := SSet.uliftFunctor.{u + 1, u}
    let Rf := R.nativeRestrict f
    let Rg := R.nativeRestrict g
    let ν := (functorIso_ulift.{u, u + 1} e).postcomp R.diagram
    let rF := smallLeftUnstraighteningLift Rf.diagram Rf.comparison
    let rG := smallLeftUnstraighteningLift Rg.diagram Rg.comparison
    let z := rF ≫ smallUnstraighteningFunctorHom ν.hom
    ∃ (a : pullback p f ⟶ pullback p g)
      (ha : a ≫ pullback.snd p g = pullback.snd p f)
      (L : FunctorIso (U.map (pullback.fst p f)) (U.map (a ≫ pullback.fst p g))),
      HEq (L.postcomp (U.map p)) ((functorIso_ulift.{u, u + 1} e).precomp
        (U.map (pullback.snd p f))) ∧
      ∃ (hz : z ≫ smallLeftUnstraighteningProjection Rg.diagram = pullback.snd p f)
        (ht : (a ≫ rG) ≫ smallLeftUnstraighteningProjection Rg.diagram = pullback.snd p f),
        Nonempty (VertexIso
          (relativeFunctorVertex (smallLeftUnstraighteningProjection Rg.diagram) (pullback.snd p f) z hz)
          (relativeFunctorVertex (smallLeftUnstraighteningProjection Rg.diagram) (pullback.snd p f) (a ≫ rG) ht)) := by
  intro E B K hB p hp R f g e
  dsimp only
  let U := SSet.uliftFunctor.{u + 1, u}
  let ν := (functorIso_ulift.{u, u + 1} e).postcomp R.diagram
  obtain ⟨a, ha, L, P, hL, hP⟩ := exists_nativePullbackPointedIsoLiftData p R e
  obtain ⟨W, h₀, h₁, hW⟩ := exists_transportRepresentation_arrowPrism_of_pointedIso
    (U.map (pullback.snd p f)) (U.map (pullback.snd p g))
    (R.nativeRestrict f) (R.nativeRestrict g) (U.map a)
    (by rw [← U.map_comp, ha]) ν P hP
  obtain ⟨hz, ht, hh⟩ := smallTransportRepresentation_arrowPrismComparison
    (pullback.snd p f) (pullback.snd p g) (R.nativeRestrict f) (R.nativeRestrict g)
    a ha ν W h₀ h₁ hW
  exact ⟨a, ha, L, hL, hz, ht, hh⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

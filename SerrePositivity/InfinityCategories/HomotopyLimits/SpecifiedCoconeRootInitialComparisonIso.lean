module

public import
  SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootMiddleInitialHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.HomotopyIsoPostcomp
public import SerrePositivity.InfinityCategories.HomotopyLimits.ArrowIdentityComposition

/-!
概要：左右の元の初期 Hom 族を、同じ固定終点空間で三つの比較の積により結ぶ。
方針：左の逆・中央・右の円柱の同型を合成し、各評価像の恒等性を保持する。
規約：評価の恒等性は射の類としての主張。使われ方：共通 end 内の経路の整合性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "L" => specifiedCoconeLeftInitialHomFamily hp p c hc dB dC y
local notation "R" => specifiedCoconeRootedInitialHomFamily hp p c hc dB dC y
local notation "HL" => specifiedCoconeRootStartInitialHomotopy hp p c hc dB dC y
local notation "HM" => specifiedCoconeRootMiddleInitialHomotopy hp p c hc dB dC y
local notation "HR" => specifiedCoconeRootEndInitialHomotopy hp p c hc dB dC y
local notation "IL" => functorIsoOfSimplicialHomotopy HL
local notation "IM" => functorIsoOfSimplicialHomotopy HM
local notation "IR" => functorIsoOfSimplicialHomotopy HR
local notation "ev" => leftFibrationInitialEvaluation q c y
local notation "z" => specifiedCoconeCommonHomFamily hp p c hc dB dC y
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y

/-- 同じ三つの円柱から得る、元の左右の初期 Hom 族の比較同型。 -/
def specifiedCoconeRootInitialComparisonIso : FunctorIso L R :=
  (IL).symm ≪≫ IM ≪≫ IR

/-- 可変終点評価の像は、元の同じ共通部分の全族の恒等射である。 -/
lemma specifiedCoconeRootInitialComparisonIso_evaluation_hom_arrow :
    Arrow.mk (FunctorIso.postcomp
      (specifiedCoconeRootInitialComparisonIso hp p c hc dB dC y) ev).hom =
        Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex z))) := by
  let F := (hoFunctor.map ((ihom T).map ev)).toFunctor
  have hL : Arrow.mk (F.map (IL).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex z))) := by
    apply homotopyIso_postcomp_constant_arrow HL ev z
    rw [specifiedCoconeRootStartInitialHomotopy_evaluation,
      specifiedCoconeLeftInitialHomFamily_evaluation]
  have hM : Arrow.mk (F.map (IM).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex z))) :=
    homotopyIso_postcomp_constant_arrow HM ev z
      (specifiedCoconeRootMiddleInitialHomotopy_evaluation hp p c hc dB dC y)
  have hR : Arrow.mk (F.map (IR).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex z))) := by
    apply homotopyIso_postcomp_constant_arrow HR ev z
    rw [specifiedCoconeRootEndInitialHomotopy_evaluation,
      specifiedCoconeRootedInitialHomFamily_evaluation]
  rw [functorIso_postcomp_hom, specifiedCoconeRootInitialComparisonIso]
  exact functor_threeFactors_identity_arrow F IL IM IR
    (HomotopyCategory.mk (functorVertex z)) hL hM hR

/-- 底の最初の二比較は恒等となり、三因子の像は元の右比較の像そのもの。 -/
lemma specifiedCoconeRootInitialComparisonIso_base_hom_arrow :
    Arrow.mk (FunctorIso.postcomp
      (specifiedCoconeRootInitialComparisonIso hp p c hc dB dC y)
        (leftFibrationInitialProjection q c y)).hom =
      Arrow.mk (FunctorIso.postcomp IR (leftFibrationInitialProjection q c y)).hom := by
  let P := leftFibrationInitialProjection q c y
  let F := (hoFunctor.map ((ihom T).map P)).toFunctor
  have hA₀ := congrArg (fun m ↦ SSet.ι₀ ≫ m)
    (specifiedCoconeRootStartInitialHomotopy_base hp p c hc dB dC y)
  simp only [← Category.assoc, (HL).h₀, SSet.ι₀_fst, Category.id_comp] at hA₀
  have hL : Arrow.mk (F.map (IL).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex (L ≫ P)))) :=
    homotopyIso_postcomp_constant_arrow HL P (L ≫ P)
      (specifiedCoconeRootStartInitialHomotopy_base hp p c hc dB dC y)
  have hm : (HM).h ≫ P = fst T Δ[1] ≫ (L ≫ P) :=
    (specifiedCoconeRootMiddleInitialHomotopy_base hp p c hc dB dC y).trans
      (congrArg (fun m ↦ fst T (Δ[1] : SSet.{u + 1}) ≫ m) hA₀)
  have hM : Arrow.mk (F.map (IM).hom) =
      Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex (L ≫ P)))) :=
    homotopyIso_postcomp_constant_arrow HM P (L ≫ P) hm
  rw [functorIso_postcomp_hom, functorIso_postcomp_hom,
    specifiedCoconeRootInitialComparisonIso]
  exact functor_threeFactors_first_two_identity_arrow F IL IM IR
    (HomotopyCategory.mk (functorVertex (L ≫ P))) hL hM

end
end SerrePositivity.InfinityCategories.HomotopyLimits

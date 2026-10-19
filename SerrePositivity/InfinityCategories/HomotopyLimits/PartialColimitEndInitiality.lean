module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconePointHomInitiality
public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitHomEnd
public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitSpecifiedPathCocone

/-!
概要：貼った余錐の余極限性を、共通の左 Hom の end への全 Hom の族の同値性へ正確に帰着する。
方針：既存の余錐空間から end への実際の同値を消去し、点の Hom の始対象性判定を適用する。
規約：end 比較の同値性は結論せず、残る検証条件として明示。使われ方：指定経路で構成した余錐の検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D X : SSet.{u}} [Quasicategory X] {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ X)
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (hB : IsColimitCone dB)
  (dC : JoinCocone (j ≫ p)) (hC : IsColimitCone dC)

/-- 任意の元の余錐の全 Hom の族を、部分余極限頂点の共通 end へ写す実際の射。 -/
def partialColimitHomFamilyToEnd (d : JoinCocone p) (y : X _⦋0⦌) :
    pinchedHomLeft d.vertex y ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (partialColimitHomCospan hp p y c hc dB dC) :=
  coconePointHomFamily d y ≫ partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC

/-- 元の余錐の余極限性は、共通 end への全 Hom の族が全終点で同値となることと同値。 -/
lemma isColimitCone_iff_partialColimitHomFamilyToEnd [Mono g] (d : JoinCocone p) :
    IsColimitCone d ↔ ∀ y : X _⦋0⦌,
      IsSimplicialHomotopyEquivalence (partialColimitHomFamilyToEnd hp p c hc dB hB dC hC d y) := by
  constructor
  · intro hd y
    have : KanComplex (coconeMappingSpace p y) := coconeMappingSpace_kanComplex p y
    exact (coconePointHomFamily_homotopyEquivalence d hd y).comp
      (partialColimitCoconeToHomEnd_homotopyEquivalence hp p y c hc dB hB dC hC)
  · intro h
    let H := fun y ↦ weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
      (partialColimitHomCospan hp p y c hc dB dC)
    let (y : X _⦋0⦌) : KanComplex (H y) := bousfieldKanWeightedSections_kanComplex _
    exact isColimitCone_of_pointHomFamily_comparison d H
      (fun y ↦ partialColimitCoconeToHomEnd hp p y c hc dB hB dC hC)
      (fun y ↦ partialColimitCoconeToHomEnd_homotopyEquivalence hp p y c hc dB hB dC hC) h

/-- 同じ全 Hom の族を、ホモトピー逆を選ぶ前の共通 path end へ写す射。 -/
def partialColimitHomFamilyToPathEnd (d : JoinCocone p) (y : X _⦋0⦌) :
    pinchedHomLeft d.vertex y ⟶ partialColimitHomPathEnd hp p y c hc dB dC :=
  coconePointHomFamily d y ≫ partialColimitCoconeHomEndComparison hp p y c hc dB hB dC hC

/-- 共通 path end への全 Hom の族の同値性も、元の余錐の余極限性の必要十分条件。 -/
lemma isColimitCone_iff_partialColimitHomFamilyToPathEnd [Mono g] (d : JoinCocone p) :
    IsColimitCone d ↔ ∀ y : X _⦋0⦌,
      IsSimplicialHomotopyEquivalence
        (partialColimitHomFamilyToPathEnd hp p c hc dB hB dC hC d y) := by
  constructor
  · intro hd y
    have : KanComplex (coconeMappingSpace p y) := coconeMappingSpace_kanComplex p y
    exact (coconePointHomFamily_homotopyEquivalence d hd y).comp
      (partialColimitCoconeHomEndComparison_homotopyEquivalence hp p y c hc dB hB dC hC)
  · intro h
    exact isColimitCone_of_pointHomFamily_comparison d
      (fun y ↦ partialColimitHomPathEnd hp p y c hc dB dC)
      (fun y ↦ partialColimitCoconeHomEndComparison hp p y c hc dB hB dC hC)
      (fun y ↦ partialColimitCoconeHomEndComparison_homotopyEquivalence hp p y c hc dB hB dC hC) h

end
end SerrePositivity.InfinityCategories.HomotopyLimits

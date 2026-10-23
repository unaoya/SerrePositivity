module

public import SerrePositivity.InfinityCategories.F1.Transport.SimplexNervePushout

/-!
概要：単射への反転関手の制限は inner fibration。
方針：内部 Hom の制限と全部分複体の包含の合成から、単射の後合成を消去する。
規約：標的の quasicategory 性と底の単射性のみを仮定する。
使われ方：局所化比較の相対的なホーン充填性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 単射による後合成が inner fibration なら、元の射も inner fibration。 -/
lemma innerFibration_of_comp_mono {A B C : SSet.{u}} (p : A ⟶ B) (j : B ⟶ C)
    [Mono j] [InnerFibration (p ≫ j)] : InnerFibration p := by
  constructor
  intro X Y i hi
  have : HasLiftingProperty i (p ≫ j) := InnerFibration.mem (q := p ≫ j) i hi
  constructor
  intro a b sq
  have hs : CommSq a i (p ≫ j) (b ≫ j) := by
    constructor
    rw [← Category.assoc, sq.w, Category.assoc]
  refine CommSq.HasLift.mk' {
    l := hs.lift
    fac_left := hs.fac_left
    fac_right := ?_ }
  apply (cancel_mono j).mp
  rw [Category.assoc, hs.fac_right]

/-- 単射に沿う反転関手の制限は、指定された比較を保って内ホーンを充填する。 -/
instance transportSimplexInvertingRestriction_innerFibration {B D : SSet.{u}}
    (f : B ⟶ D) [Mono f] (E : SSet.{u}) [Quasicategory E] :
    InnerFibration (transportSimplexInvertingRestriction f E) := by
  let j := (invertingFunctors (nerve (TransportSimplexCategory B)) E
    (transportSimplexInitialEdges B)).ι
  have hh : innerFibrations (transportSimplexInvertingRestriction f E ≫ j) := by
    rw [show j = (invertingFunctors (nerve (TransportSimplexCategory B)) E
      (transportSimplexInitialEdges B)).ι from rfl, transportSimplexInvertingRestriction_ι]
    apply innerFibrations.comp_mem
    · change innerFibrations (fullSubcomplexOnVertices
        ((ihom (nerve (TransportSimplexCategory D))).obj E)
        (IsInvertingFunctorVertex _ E (transportSimplexInitialEdges D))).ι
      exact mem_innerFibrations _
    · exact mem_innerFibrations _
  have : InnerFibration (transportSimplexInvertingRestriction f E ≫ j) := ⟨hh⟩
  exact innerFibration_of_comp_mono (transportSimplexInvertingRestriction f E) j

end SerrePositivity.InfinityCategories

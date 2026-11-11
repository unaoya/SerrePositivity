module
public import SerrePositivity.KST.SConstruction.SClosedFamilies
public import SerrePositivity.KST.SConstruction.SCofiberIso

/-! # S_n と閉じた全部分圏の交換同型
概要：S_n A を、全 Ar 成分が A に入る S_n C の全部分圏と同定する。
方針：全単体の族の持ち上げを逆射にし、包含の単射性で逆律を検査する。
規約：比較は単体集合の厳密な同型。使われ方：相対加法性の各行の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 完全な単射の S_n による後合成も単射。 -/
lemma sPostcompCofiber_mono (n : ℕ) {C D : SSet.{u}} [Quasicategory D]
    (f : C ⟶ D) [Mono f] (hf : PreservesCofiberData f) : Mono (sPostcompCofiber n f hf) := by
  have : Mono ((gappedSubcomplex n C).ι ≫ (ihom (arNerve n)).map f) := inferInstance
  exact mono_of_mono_fac (sPostcompCofiber_ι n f hf)

/-- S_n A の像の全 Ar 成分は A の所属条件を満たす。 -/
lemma sClosedInclusion_vertex {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X)
    (v : (sConstruction n (closedSubcategory P)) _⦋0⦌) :
    (sClosedPredicate n P).predicate
      (((sEndofunctor n).map (closedStableInclusion P)).val.app (Opposite.op ⦋0⦌) v) := by
  intro a
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sPostcompCofiber_gapped_evaluate n
      (closedStableInclusion P).val (closedStableInclusion P).property a)
      (Opposite.op ⦋0⦌)) v
  change P.predicate ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app (Opposite.op ⦋0⦌)
    ((((sEndofunctor n).map (closedStableInclusion P)).val.app (Opposite.op ⦋0⦌) v).val))
  exact (congrArg P.predicate h).mpr (closedSubcategory_vertex P
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a).app (Opposite.op ⦋0⦌) v.val))

/-- S_n A から S_n C 内の全成分の所属条件を持つ全部分圏への比較。 -/
def sClosedComparison {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X) :
    sConstruction n (closedSubcategory P) ⟶ closedSubcategory (sClosedPredicate n P) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (sClosedPredicate n P).predicate
    ((sEndofunctor n).map (closedStableInclusion P)).val (sClosedInclusion_vertex n P)

/-- 比較は S_n による元の包含の後合成と一致する。 -/
lemma sClosedComparison_inclusion {X : StableModel.{u}} (n : ℕ)
    (P : ClosedStablePredicate X) :
    sClosedComparison n P ≫ (closedStableInclusion (sClosedPredicate n P)).val =
      ((sEndofunctor n).map (closedStableInclusion P)).val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _

/-- 全成分が A に入る S_n C の全部分圏を S_n A に戻す。 -/
def sClosedInverse {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X) :
    closedSubcategory (sClosedPredicate n P) ⟶ sConstruction n (closedSubcategory P) :=
  sClosedFamilyLift n P (closedStableInclusion (sClosedPredicate n P)).val
    (closedSubcategory_vertex (sClosedPredicate n P))

/-- 逆比較は包含の後で元の図式を厳密に保持する。 -/
lemma sClosedInverse_inclusion {X : StableModel.{u}} (n : ℕ)
    (P : ClosedStablePredicate X) :
    sClosedInverse n P ≫ ((sEndofunctor n).map (closedStableInclusion P)).val =
      (closedStableInclusion (sClosedPredicate n P)).val :=
  sClosedFamilyLift_inclusion n P _ _

/-- S_n と閉じた全部分圏は全高次単体を含めて厳密に交換する。 -/
def sClosedIso {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X) :
    sConstruction n (closedSubcategory P) ≅ closedSubcategory (sClosedPredicate n P) where
  hom := sClosedComparison n P
  inv := sClosedInverse n P
  hom_inv_id := by
    have : Mono (closedStableInclusion P).val :=
      inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X.carrier P.predicate).ι)
    have : Mono (((sEndofunctor n).map (closedStableInclusion P)).val) :=
      sPostcompCofiber_mono n (closedStableInclusion P).val (closedStableInclusion P).property
    apply inverse_comp_of_commuting_mono
      (((sEndofunctor n).map (closedStableInclusion P)).val)
      (closedStableInclusion (sClosedPredicate n P)).val
      (sClosedComparison n P) (sClosedInverse n P) (𝟙 _) (𝟙 _)
    · exact (sClosedComparison_inclusion n P).trans (Category.comp_id _).symm
    · exact (sClosedInverse_inclusion n P).trans (Category.comp_id _).symm
    · exact Category.id_comp _
  inv_hom_id := by
    have : Mono (closedStableInclusion (sClosedPredicate n P)).val :=
      inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (sClosedPredicate n P).predicate).ι)
    apply inverse_comp_of_commuting_mono
      (closedStableInclusion (sClosedPredicate n P)).val
      (((sEndofunctor n).map (closedStableInclusion P)).val)
      (sClosedInverse n P) (sClosedComparison n P) (𝟙 _) (𝟙 _)
    · exact (sClosedInverse_inclusion n P).trans (Category.comp_id _).symm
    · exact (sClosedComparison_inclusion n P).trans (Category.comp_id _).symm
    · exact Category.id_comp _

end SerrePositivity.KST.SConstruction

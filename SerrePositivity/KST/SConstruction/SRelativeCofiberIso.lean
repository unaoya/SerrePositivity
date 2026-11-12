module
public import SerrePositivity.KST.SConstruction.SRelativePredicate

/-! # S_n と相対 cofiber 図式の交換同型
概要：S_n E(A,C,B) を E(S_n A,S_n C,S_n B) と厳密に比較する。
方針：全部分圏との交換と、全 cofiber 図式の転置の相対条件への制限を合成する。
規約：S_n A/B は全 Ar 成分の所属条件による模型。使われ方：相対加法性の行。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel
open scoped Simplicial

/-- S/cofiber 交換同型の相対条件を満たす全部分圏への制限。 -/
def sRelativeRestrictionIso {X : StableModel.{u}} (n : ℕ) (A B : ClosedStablePredicate X) :
    closedSubcategory (sClosedPredicate n (relativeCofiberPredicate A B)) ≅
      relativeCofiberDiagrams (sClosedPredicate n A) (sClosedPredicate n B) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fullSubcomplexIso (sCofiberIso n X.carrier)
    (sClosedPredicate n (relativeCofiberPredicate A B)).predicate
    (relativeCofiberPredicate (sClosedPredicate n A) (sClosedPredicate n B)).predicate
    (sCofiber_relativePredicate_iff n A B)

/-- 相対制限は元の S/cofiber の転置と包含後に厳密に一致する。 -/
lemma sRelativeRestrictionIso_inclusion {X : StableModel.{u}} (n : ℕ)
    (A B : ClosedStablePredicate X) :
    (sRelativeRestrictionIso n A B).hom ≫
        (relativeCofiberInclusion (sClosedPredicate n A) (sClosedPredicate n B)).val =
      (closedStableInclusion (sClosedPredicate n (relativeCofiberPredicate A B))).val ≫
        (sCofiberIso n X.carrier).hom := rfl

/-- 相対図式の S_n と S_n C 内の相対 cofiber 図式は厳密に同型。 -/
def sRelativeCofiberIso {X : StableModel.{u}} (n : ℕ) (A B : ClosedStablePredicate X) :
    sConstruction n (relativeCofiberDiagrams A B) ≅
      relativeCofiberDiagrams (sClosedPredicate n A) (sClosedPredicate n B) :=
  (sClosedIso n (relativeCofiberPredicate A B)) ≪≫ sRelativeRestrictionIso n A B

/-- 相対交換の順射は元の完全な包含と S/cofiber 交換に厳密に可換。 -/
lemma sRelativeCofiberIso_inclusion {X : StableModel.{u}} (n : ℕ)
    (A B : ClosedStablePredicate X) :
    (sRelativeCofiberIso n A B).hom ≫
        (relativeCofiberInclusion (sClosedPredicate n A) (sClosedPredicate n B)).val =
      ((sEndofunctor n).map (relativeCofiberInclusion A B)).val ≫
        (sCofiberIso n X.carrier).hom := by
  calc
    _ = (sClosedIso n (relativeCofiberPredicate A B)).hom ≫
        ((sRelativeRestrictionIso n A B).hom ≫
          (relativeCofiberInclusion (sClosedPredicate n A) (sClosedPredicate n B)).val) :=
      Category.assoc _ _ _
    _ = (sClosedIso n (relativeCofiberPredicate A B)).hom ≫
        ((closedStableInclusion (sClosedPredicate n (relativeCofiberPredicate A B))).val ≫
          (sCofiberIso n X.carrier).hom) :=
      congrArg (fun f => (sClosedIso n (relativeCofiberPredicate A B)).hom ≫ f)
        (sRelativeRestrictionIso_inclusion n A B)
    _ = _ := (Category.assoc _ _ _).symm.trans
      (congrArg (fun f => f ≫ (sCofiberIso n X.carrier).hom)
        (sClosedComparison_inclusion n (relativeCofiberPredicate A B)))

/-- 相対 S/cofiber 交換も完全関手の圏での同型。 -/
def sRelativeCofiberStableIso {X : StableModel.{u}} (n : ℕ) (A B : ClosedStablePredicate X) :
    sStableModel n (relativeCofiberStableModel A B) ≅
      relativeCofiberStableModel (sClosedPredicate n A) (sClosedPredicate n B) where
  hom := ⟨(sRelativeCofiberIso n A B).hom, by
    have : IsIso (sRelativeCofiberIso n A B).hom := inferInstance
    exact (preservesSConstructionData_of_trivialKanFibration _).toCofiberData⟩
  inv := ⟨(sRelativeCofiberIso n A B).inv, by
    have : IsIso (sRelativeCofiberIso n A B).inv := inferInstance
    exact (preservesSConstructionData_of_trivialKanFibration _).toCofiberData⟩
  hom_inv_id := Subtype.ext (sRelativeCofiberIso n A B).hom_inv_id
  inv_hom_id := Subtype.ext (sRelativeCofiberIso n A B).inv_hom_id

/-- 完全な相対交換は全 cofiber 図式への包含を厳密に保つ。 -/
lemma sRelativeCofiberStableIso_inclusion {X : StableModel.{u}} (n : ℕ)
    (A B : ClosedStablePredicate X) :
    (sRelativeCofiberStableIso n A B).hom ≫
        relativeCofiberInclusion (sClosedPredicate n A) (sClosedPredicate n B) =
      (sEndofunctor n).map (relativeCofiberInclusion A B) ≫ (sCofiberStableIso n X).hom :=
  Subtype.ext (sRelativeCofiberIso_inclusion n A B)

end SerrePositivity.KST.SConstruction

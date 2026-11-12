module
public import SerrePositivity.KST.SConstruction.SClosedIso
public import SerrePositivity.KST.SConstruction.SCofiberStableIso

/-! # 完全関手としての S_n と全部分圏の交換
概要：全 Ar 成分による厳密な比較を安定な入力の圏の同型に持ち上げる。
方針：比較の自明 Kan ファイブレーション性から完全性を得る。
規約：底の射は全高次単体の既存の比較。使われ方：相対加法性の反復。
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

/-- S_n と閉じた全部分圏の交換は完全関手の圏での同型。 -/
def sClosedStableIso {X : StableModel.{u}} (n : ℕ) (P : ClosedStablePredicate X) :
    sStableModel n (closedStableModel P) ≅ closedStableModel (sClosedPredicate n P) where
  hom := ⟨(sClosedIso n P).hom, by
    have : IsIso (sClosedIso n P).hom := inferInstance
    exact (preservesSConstructionData_of_trivialKanFibration _).toCofiberData⟩
  inv := ⟨(sClosedIso n P).inv, by
    have : IsIso (sClosedIso n P).inv := inferInstance
    exact (preservesSConstructionData_of_trivialKanFibration _).toCofiberData⟩
  hom_inv_id := Subtype.ext (sClosedIso n P).hom_inv_id
  inv_hom_id := Subtype.ext (sClosedIso n P).inv_hom_id

/-- 完全な比較は元の包含の S_n への作用と厳密に可換。 -/
lemma sClosedStableIso_inclusion {X : StableModel.{u}} (n : ℕ)
    (P : ClosedStablePredicate X) :
    (sClosedStableIso n P).hom ≫ closedStableInclusion (sClosedPredicate n P) =
      (sEndofunctor n).map (closedStableInclusion P) :=
  Subtype.ext (sClosedComparison_inclusion n P)

/-- Ar 成分の完全な評価は入力の完全関手に関して自然。 -/
lemma sStableEvaluation_naturality (n : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (a : (arNerve n) _⦋0⦌) :
    (sEndofunctor n).map f ≫ sStableEvaluation n Y a =
      sStableEvaluation n X a ≫ f :=
  Subtype.ext (sPostcompCofiber_gapped_evaluate n f.val f.property a)

/-- 閉じた全部分圏への完全関手は包含との合成で判定できる。 -/
lemma closedStableInclusion_cancel {X Y : StableModel.{u}} (P : ClosedStablePredicate Y)
    {f g : X ⟶ closedStableModel P}
    (h : f ≫ closedStableInclusion P = g ≫ closedStableInclusion P) : f = g := by
  have : Mono (closedStableInclusion P).val :=
    inferInstanceAs (Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y.carrier P.predicate).ι)
  apply Subtype.ext
  apply (cancel_mono (closedStableInclusion P).val).1
  exact congrArg Subtype.val h

end SerrePositivity.KST.SConstruction

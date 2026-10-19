module
public import SerrePositivity.KST.SConstruction.SCofiberIso
public import SerrePositivity.KST.SConstruction.CoreAdditivity

/-! # 完全関手としての S/cofiber 交換
概要：S/cofiber の交換同型を安定な入力の圏へ持ち上げ、各角の完全な評価を照合する。
方針：厳密な同型の自明ファイブレーション性から完全性を得る。
規約：底の比較は元の転置。使われ方：有限反復の加法性と自然性。
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

/-- S_n と cofiber 図式の交換は安定な入力の圏でも厳密な同型。 -/
def sCofiberStableIso (n : ℕ) (X : StableModel.{u}) :
    sStableModel n (cofiberStableModel X) ≅ cofiberStableModel (sStableModel n X) where
  hom := ⟨(sCofiberIso n X.carrier).hom, by
    have : IsIso (sCofiberIso n X.carrier).hom := inferInstance
    exact (preservesSConstructionData_of_trivialKanFibration _).toCofiberData⟩
  inv := ⟨(sCofiberIso n X.carrier).inv, by
    have : IsIso (sCofiberIso n X.carrier).inv := inferInstance
    exact (preservesSConstructionData_of_trivialKanFibration _).toCofiberData⟩
  hom_inv_id := Subtype.ext (sCofiberIso n X.carrier).hom_inv_id
  inv_hom_id := Subtype.ext (sCofiberIso n X.carrier).inv_hom_id

/-- 交換同型は全ての角の完全な評価と厳密に可換。 -/
lemma sCofiberStableIso_evaluation (n : ℕ) (X : StableModel.{u})
    (q : (Δ[1] ⊗ Δ[1] : SSet.{u}).obj (Opposite.op ⦋0⦌)) :
    (sCofiberStableIso n X).hom ≫ cofiberStableEvaluation (sStableModel n X) q =
      (sEndofunctor n).map (cofiberStableEvaluation X q) :=
  Subtype.ext (sCofiberComparison_evaluation n X.carrier q)

/-- 交換同型は subobject の完全関手と厳密に可換。 -/
lemma sCofiberStableIso_subobject (n : ℕ) (X : StableModel.{u}) :
    (sCofiberStableIso n X).hom ≫ cofiberStableSubobject (sStableModel n X) =
      (sEndofunctor n).map (cofiberStableSubobject X) :=
  sCofiberStableIso_evaluation n X _

/-- 交換同型は quotient の完全関手と厳密に可換。 -/
lemma sCofiberStableIso_quotient (n : ℕ) (X : StableModel.{u}) :
    (sCofiberStableIso n X).hom ≫ cofiberStableQuotient (sStableModel n X) =
      (sEndofunctor n).map (cofiberStableQuotient X) :=
  sCofiberStableIso_evaluation n X _

/-- 各 S_n の後でも交換比較の任意の有限反復実現は局所化同型。 -/
lemma sCofiberStableIso_realization_localized_isIso (r n : ℕ) (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor r).map (sCofiberStableIso n X).hom)) := by
  infer_instance

end SerrePositivity.KST.SConstruction

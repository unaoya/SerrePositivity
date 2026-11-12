module
public import SerrePositivity.KST.SConstruction.SClosedStableIso
public import SerrePositivity.KST.SConstruction.RelativeCofiberModel
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FullSubcomplexIso

/-! # S/cofiber 交換による相対条件の照合
概要：相対 E(A,C,B) の全 Ar 成分の条件を、S_n C 内の相対条件と照合する。
方針：subobject・quotient の厳密な交換式を各 Ar 成分で評価する。
規約：部分圏は全 Ar 成分の所属条件。使われ方：相対 S/cofiber 交換の制限。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- S/cofiber 交換後の subobject の各成分は元の各成分の subobject。 -/
lemma sCofiberStableIso_subobject_component (n : ℕ) (X : StableModel.{u})
    (a : (arNerve n) _⦋0⦌) :
    (sCofiberStableIso n X).hom ≫ cofiberStableSubobject (sStableModel n X) ≫
        sStableEvaluation n X a =
      sStableEvaluation n (cofiberStableModel X) a ≫ cofiberStableSubobject X := by
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ sStableEvaluation n X a) (sCofiberStableIso_subobject n X))).trans
      (sStableEvaluation_naturality n (cofiberStableSubobject X) a)

/-- S/cofiber 交換後の quotient の各成分は元の各成分の quotient。 -/
lemma sCofiberStableIso_quotient_component (n : ℕ) (X : StableModel.{u})
    (a : (arNerve n) _⦋0⦌) :
    (sCofiberStableIso n X).hom ≫ cofiberStableQuotient (sStableModel n X) ≫
        sStableEvaluation n X a =
      sStableEvaluation n (cofiberStableModel X) a ≫ cofiberStableQuotient X := by
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (fun f => f ≫ sStableEvaluation n X a) (sCofiberStableIso_quotient n X))).trans
      (sStableEvaluation_naturality n (cofiberStableQuotient X) a)

/-- 全成分の相対条件は S/cofiber 交換で S_n C の相対条件に一致する。 -/
lemma sCofiber_relativePredicate_iff {X : StableModel.{u}} (n : ℕ)
    (A B : ClosedStablePredicate X) (v : (sConstruction n (cofiberDiagrams X.carrier)) _⦋0⦌) :
    (sClosedPredicate n (relativeCofiberPredicate A B)).predicate v ↔
      (relativeCofiberPredicate (sClosedPredicate n A) (sClosedPredicate n B)).predicate
        ((sCofiberIso n X.carrier).hom.app (Opposite.op ⦋0⦌) v) := by
  have hs (a : (arNerve n) _⦋0⦌) := congrArg
    (fun f : sStableModel n (cofiberStableModel X) ⟶ X => f.val.app (Opposite.op ⦋0⦌) v)
    (sCofiberStableIso_subobject_component n X a)
  have hq (a : (arNerve n) _⦋0⦌) := congrArg
    (fun f : sStableModel n (cofiberStableModel X) ⟶ X => f.val.app (Opposite.op ⦋0⦌) v)
    (sCofiberStableIso_quotient_component n X a)
  constructor
  · intro h
    exact ⟨fun a => (congrArg A.predicate (hs a)).mpr (h a).1,
      fun a => (congrArg B.predicate (hq a)).mpr (h a).2⟩
  · intro h a
    exact ⟨(congrArg A.predicate (hs a)).mp (h.1 a),
      (congrArg B.predicate (hq a)).mp (h.2 a)⟩

end SerrePositivity.KST.SConstruction

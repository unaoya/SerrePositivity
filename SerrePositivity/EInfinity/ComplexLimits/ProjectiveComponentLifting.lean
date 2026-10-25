module

public import SerrePositivity.EInfinity.ComplexLimits.CodiskFibrations
public import Mathlib.CategoryTheory.LiftingProperties.Adjunction

/-!
# 射影 cofibration の各次数の持ち上げ

概要：射影 cofibration の各成分は任意の全射加群射に対して左持ち上げ性を持つ。
方針：評価と可縮 codisk の随伴で、実複体の持ち上げ性へ移す。
規約：始域・終域の cofibrancy や有界性を要求しない。
使われ方：固定底の内部 Hom の相対全射性。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A]

/-- 概要：射影 cofibration の成分は全射に対して持ち上がる。
方針：全射の codisk 像が trivial fibration であることを随伴で使う。
規約：元の成分射自身の持ち上げ性を述べる。
使われ方：次数付き Hom の可換平方を成分ごとに埋める。 -/
lemma projectiveCofibration_component_lifting {P Q : Complex A} (i : P ⟶ Q)
    (hi : (projectiveGeneratingCofibrations A).rlp.llp i)
    (n : ℤ) {M N : ModuleCat.{u} A} (p : M ⟶ N) [Epi p] :
    HasLiftingProperty (i.f n) p := by
  apply ((codiskAdjunction A n).hasLiftingProperty_iff i p).2
  apply hi
  rw [projectiveGeneratingCofibrations_rlp]
  exact ⟨codiskFunctor_map_fibration A n p, codiskFunctor_map_quasiIso A n p⟩

end SerrePositivity.EInfinity.ComplexLimits

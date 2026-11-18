module

public import SerrePositivity.EInfinity.PowerOperation.MayClosedHomology
public import SerrePositivity.EInfinity.PowerOperation.MayZeroHomology

/-!
# May の全次数の類と零次の単位射の類の比較

May, Proposition 2.3(iii) の零次計算を全次数の構成へ接続する補助。
元の kernel の商と単位複体の指定元を使い、別のホモロジー同型を選ばない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.HomologyZero
variable {k : Type u} [CommRing k]

lemma mayClosedClass_zero_eq_classMap (K : Complex k) (a : MayClosed K 0) :
    mayClosedClass K 0 a = _root_.SerrePositivity.HomologyZero.classMap K a := rfl

lemma mayClosedClass_cycleFromUnit (K : Complex k) (f : 𝟙_ (Complex k) ⟶ K) :
    mayClosedClass K 0 (cycleFromUnit K f) = _root_.SerrePositivity.HomologyZero.unitClass K f := rfl

end SerrePositivity.EInfinity.PowerOperation

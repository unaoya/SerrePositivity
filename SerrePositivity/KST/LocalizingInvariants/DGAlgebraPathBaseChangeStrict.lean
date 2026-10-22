module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBaseChangeTraces
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackComparisonQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveQuasiIso
public import SerrePositivity.KST.LocalizingInvariants.CochainPullbackBounds

/-!
概要：元の経路で結ばれた二つの通常底変更を、元の両脚・経路を保つ実準同型で結ぶ。
方針：右脚が次数全射な通常 pullback 比較を、同じ実共通模型へ続ける。
規約：指定された実底経路の像を保持。使われ方：二切断の分子・分母側の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
variable (R : Type u) [CommRing R] {P B U : Mon (Complex R)}
  (a b : P ⟶ B) (q : U ⟶ B) (w : Path.Witness R a b)

def firstStrict : MonoidPullback.obj a q ⟶ common R a q :=
  HomotopyPullbackModel.comparison R a q ≫ first R a q

def secondStrict : MonoidPullback.obj b q ⟶ common R a q :=
  HomotopyPullbackModel.comparison R b q ≫ second R a b q w

lemma firstStrict_quasiIso [Epi q.hom] : QuasiIso (firstStrict R a q).hom :=
  quasiIso_comp _ _ (hφ := HomotopyPullbackModel.comparison_quasiIso_right R a q)
    (hφ' := first_quasiIso R a q)

lemma secondStrict_quasiIso [Epi q.hom] : QuasiIso (secondStrict R a b q w).hom :=
  quasiIso_comp _ _ (hφ := HomotopyPullbackModel.comparison_quasiIso_right R b q)
    (hφ' := second_quasiIso R a b q w)

lemma firstStrict_base : firstStrict R a q ≫ base R a q = MonoidPullback.fst a q := by
  rw [firstStrict, Category.assoc, first_base, HomotopyPullbackModel.comparison_left]

lemma secondStrict_base : secondStrict R a b q w ≫ base R a q = MonoidPullback.fst b q := by
  rw [secondStrict, Category.assoc, second_base, HomotopyPullbackModel.comparison_left]

lemma firstStrict_upper : firstStrict R a q ≫ upper R a q = MonoidPullback.snd a q := by
  rw [firstStrict, Category.assoc, first_upper, HomotopyPullbackModel.comparison_right]

lemma secondStrict_upper : secondStrict R a b q w ≫ upper R a q = MonoidPullback.snd b q := by
  rw [secondStrict, Category.assoc, second_upper, HomotopyPullbackModel.comparison_right]

lemma firstStrict_trace : firstStrict R a q ≫ trace R a q =
    MonoidPullback.fst a q ≫ a ≫ Path.diagonal R B := by
  rw [firstStrict, Category.assoc, first_trace, ← Category.assoc,
    HomotopyPullbackModel.comparison_left]

lemma secondStrict_trace : secondStrict R a b q w ≫ trace R a q =
    MonoidPullback.fst b q ≫ w.hom := by
  rw [secondStrict, Category.assoc, second_trace, ← Category.assoc,
    HomotopyPullbackModel.comparison_left]

lemma common_isConnective [P.X.IsStrictlyLE 0] [U.X.IsStrictlyLE 0] [Epi q.hom] :
    IsConnective R (common R a q) := by
  have : (MonoidPullback.obj a q).X.IsStrictlyLE 0 :=
    CochainPullback.isStrictlyLE a.hom q.hom 0
  exact (quasiIso_isConnective_iff R _ (firstStrict_quasiIso R a q)).1
    (by change (MonoidPullback.obj a q).X.IsLE 0; infer_instance)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange

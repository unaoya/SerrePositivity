module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraExtensionBaseChangeKernel
public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackFunctor

/-!
概要：元の拡大と底射の実可換正方形から、底変更後の元の両射影を保つ実射を作る。
方針：既存の実 cospan 関手を使い、元の三つの比較射と可換式を保持する。
規約：底の射の準同型性は不要。使われ方：元の二切断射の共通底への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.ExtensionBaseChange
variable (R : Type u) [CommRing R] {P U B P' U' B' : Mon (Complex R)}
  (b : P ⟶ B) (q : U ⟶ B) (b' : P' ⟶ B') (q' : U' ⟶ B')
  (v : P ⟶ P') (u : U ⟶ U') (d : B ⟶ B')
  (hb : b ≫ d = v ≫ b') (hq : q ≫ d = u ≫ q')

def cospanMap : cospan b q ⟶ cospan b' q' := cospanHomMk d v u hb hq

def map : algebra R b q ⟶ algebra R b' q' :=
  MonoidPullback.diagramMap (cospanMap R b q b' q' v u d hb hq)

lemma map_base : map R b q b' q' v u d hb hq ≫ base R b' q' = base R b q ≫ v :=
  MonoidPullback.diagramMap_fst (cospanMap R b q b' q' v u d hb hq)

lemma map_upper : map R b q b' q' v u d hb hq ≫ upper R b' q' = upper R b q ≫ u :=
  MonoidPullback.diagramMap_snd (cospanMap R b q b' q' v u d hb hq)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.ExtensionBaseChange

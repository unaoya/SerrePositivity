module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBaseChangeStrict
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveCoverLift

/-!
概要：元の底経路による二つの通常底変更を、同じ非正次数の実共通模型へ結ぶ。
方針：元の共通模型の cover へ両実比較を一意に持ち上げ、元の三成分を保持する。
規約：可逆な比較を新たな入力にしない。使われ方：非正次数 class 図式への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange
variable (R : Type u) [CommRing R] {P B U : Mon (Complex R)}
  (a b : P ⟶ B) (q : U ⟶ B) (w : Path.Witness R a b)

def nonpositiveCommon : Mon (Complex R) := connectiveCover R (common R a q)

lemma nonpositiveCommon_nonpositive : (nonpositiveCommon R a q).X.IsStrictlyLE 0 :=
  coverComplex_nonpositive R _

variable [P.X.IsStrictlyLE 0] [U.X.IsStrictlyLE 0]

local instance firstPullback_nonpositive : (MonoidPullback.obj a q).X.IsStrictlyLE 0 :=
  CochainPullback.isStrictlyLE a.hom q.hom 0

local instance secondPullback_nonpositive : (MonoidPullback.obj b q).X.IsStrictlyLE 0 :=
  CochainPullback.isStrictlyLE b.hom q.hom 0

def firstNonpositive : MonoidPullback.obj a q ⟶ nonpositiveCommon R a q :=
  connectiveCoverLift R (firstStrict R a q)

def secondNonpositive : MonoidPullback.obj b q ⟶ nonpositiveCommon R a q :=
  connectiveCoverLift R (secondStrict R a b q w)

lemma firstNonpositive_inclusion : firstNonpositive R a q ≫
    connectiveCoverInclusion R (common R a q) = firstStrict R a q :=
  connectiveCoverLift_inclusion R _

lemma secondNonpositive_inclusion : secondNonpositive R a b q w ≫
    connectiveCoverInclusion R (common R a q) = secondStrict R a b q w :=
  connectiveCoverLift_inclusion R _

lemma firstNonpositive_quasiIso [Epi q.hom] : QuasiIso (firstNonpositive R a q).hom := by
  have := connectiveCoverInclusion_quasiIso R _ (common_isConnective R a q)
  have : QuasiIso ((firstNonpositive R a q).hom ≫
      (connectiveCoverInclusion R (common R a q)).hom) := by
    change QuasiIso ((firstNonpositive R a q ≫ connectiveCoverInclusion R (common R a q)).hom)
    rw [firstNonpositive_inclusion]
    exact firstStrict_quasiIso R a q
  exact quasiIso_of_comp_right (firstNonpositive R a q).hom
    (connectiveCoverInclusion R (common R a q)).hom

lemma secondNonpositive_quasiIso [Epi q.hom] : QuasiIso (secondNonpositive R a b q w).hom := by
  have := connectiveCoverInclusion_quasiIso R _ (common_isConnective R a q)
  have : QuasiIso ((secondNonpositive R a b q w).hom ≫
      (connectiveCoverInclusion R (common R a q)).hom) := by
    change QuasiIso ((secondNonpositive R a b q w ≫ connectiveCoverInclusion R (common R a q)).hom)
    rw [secondNonpositive_inclusion]
    exact secondStrict_quasiIso R a b q w
  exact quasiIso_of_comp_right (secondNonpositive R a b q w).hom
    (connectiveCoverInclusion R (common R a q)).hom

def nonpositiveBase : nonpositiveCommon R a q ⟶ P :=
  connectiveCoverInclusion R (common R a q) ≫ base R a q

def nonpositiveUpper : nonpositiveCommon R a q ⟶ U :=
  connectiveCoverInclusion R (common R a q) ≫ upper R a q

def nonpositiveTrace : nonpositiveCommon R a q ⟶ Path.algebra R B :=
  connectiveCoverInclusion R (common R a q) ≫ trace R a q

lemma firstNonpositive_base : firstNonpositive R a q ≫ nonpositiveBase R a q =
    MonoidPullback.fst a q := by
  rw [nonpositiveBase, ← Category.assoc, firstNonpositive_inclusion, firstStrict_base]

lemma secondNonpositive_base : secondNonpositive R a b q w ≫ nonpositiveBase R a q =
    MonoidPullback.fst b q := by
  rw [nonpositiveBase, ← Category.assoc, secondNonpositive_inclusion, secondStrict_base]

lemma firstNonpositive_upper : firstNonpositive R a q ≫ nonpositiveUpper R a q =
    MonoidPullback.snd a q := by
  rw [nonpositiveUpper, ← Category.assoc, firstNonpositive_inclusion, firstStrict_upper]

lemma secondNonpositive_upper : secondNonpositive R a b q w ≫ nonpositiveUpper R a q =
    MonoidPullback.snd b q := by
  rw [nonpositiveUpper, ← Category.assoc, secondNonpositive_inclusion, secondStrict_upper]

lemma firstNonpositive_trace : firstNonpositive R a q ≫ nonpositiveTrace R a q =
    MonoidPullback.fst a q ≫ a ≫ Path.diagonal R B := by
  rw [nonpositiveTrace, ← Category.assoc, firstNonpositive_inclusion, firstStrict_trace]

lemma secondNonpositive_trace : secondNonpositive R a b q w ≫ nonpositiveTrace R a q =
    MonoidPullback.fst b q ≫ w.hom := by
  rw [nonpositiveTrace, ← Category.assoc, secondNonpositive_inclusion, secondStrict_trace]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PathBaseChange

module

public import SerrePositivity.KST.LocalizingInvariants.ConcentratedComplexHomology

/-!
概要：単次数集中複体間の指定ホモロジー射を、一意な実 cochain 射へ持ち上げる。
方針：既存のホモロジー圏同値の充満忠実性を使う。
規約：元の射と集中次数を保持。使われ方：元の π₂ 逆の実層射への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R] (d : ℤ) {M N : Complex R}
  [M.IsStrictlyGE d] [M.IsStrictlyLE d] [N.IsStrictlyGE d] [N.IsStrictlyLE d]

def concentratedHomologyLift (r : M.homology d ⟶ N.homology d) : M ⟶ N := by
  let M' : ConcentratedComplex R d := ⟨M, ⟨inferInstance, inferInstance⟩⟩
  let N' : ConcentratedComplex R d := ⟨N, ⟨inferInstance, inferInstance⟩⟩
  let r' : (concentratedComplexHomology R d).obj M' ⟶
      (concentratedComplexHomology R d).obj N' := r
  exact ((concentratedComplexHomology R d).preimage r').hom

lemma concentratedHomologyLift_homology (r : M.homology d ⟶ N.homology d) :
    homologyMap (concentratedHomologyLift R d r) d = r := by
  let M' : ConcentratedComplex R d := ⟨M, ⟨inferInstance, inferInstance⟩⟩
  let N' : ConcentratedComplex R d := ⟨N, ⟨inferInstance, inferInstance⟩⟩
  let r' : (concentratedComplexHomology R d).obj M' ⟶
      (concentratedComplexHomology R d).obj N' := r
  exact (concentratedComplexHomology R d).map_preimage r'

lemma concentratedHomology_hom_ext (a b : M ⟶ N)
    (h : homologyMap a d = homologyMap b d) : a = b := by
  have he : (ObjectProperty.homMk a :
      (⟨M, ⟨inferInstance, inferInstance⟩⟩ : ConcentratedComplex R d) ⟶
      (⟨N, ⟨inferInstance, inferInstance⟩⟩ : ConcentratedComplex R d)) =
        ObjectProperty.homMk b := (concentratedComplexHomology R d).map_injective h
  exact congrArg (fun t => t.hom) he

lemma concentratedHomologyLift_eq (a : M ⟶ N) :
    concentratedHomologyLift R d (homologyMap a d) = a :=
  concentratedHomology_hom_ext R d _ _ (concentratedHomologyLift_homology R d _)

end SerrePositivity.KST.LocalizingInvariants

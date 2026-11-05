module

public import SerrePositivity.KST.LocalizingInvariants.DGFixedNullPerfectZero
public import SerrePositivity.KST.LocalizingInvariants.DGOdotFixedNullSquare

/-!
概要：元の四辺を持つ S 内の零化四角形を、固定 ν の実零角で認証する。
方針：同じ全対象商からの延長と D-20 の presented Perf 零性を合成する。
規約：対象別の収縮を自然収縮と扱わず、Verdier 長方形の存在は別工程に残す。
使われ方：Sp-6 s2。K-S• の具体的対角・商に追加入力なしで適用する。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.LocalizingInvariants
variable (R : Type u) [CommRing R]

lemma exists_dgFixedNullCertifiedSquare
    {A B Q : PerfDGInput.{u, v} R} (i : A ⟶ B) (q : B ⟶ Q)
    (C : DGQuotient.ContractedFunctor R A Set.univ Q)
    (hC : C.toDGFunctor = i.down.comp q.down) :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{max (u + 1) v + 1}) ⟶ dgKInputInfinity.{u, v} R,
      squareBottomEdge ≫ F = SSet.yonedaEquiv.symm (coherentNerveEdge i).edge ∧
      squareRightEdge ≫ F = SSet.yonedaEquiv.symm (coherentNerveEdge q).edge ∧
      squareLeftEdge ≫ F =
        SSet.yonedaEquiv.symm (coherentNerveEdge (dgFixedNullLeft R (A := A))).edge ∧
      squareTopEdge ≫ F =
        SSet.yonedaEquiv.symm (coherentNerveEdge (dgFixedNullTop R C)).edge ∧
      IsZeroCategory (stableObject (squareVertex (F ≫ dgKInputNu R) 0 1)) := by
  obtain ⟨F, hb, hr, hl, ht⟩ := exists_dgFixedNullSquare R i q C hC
  refine ⟨F, hb, hr, hl, ht, ?_⟩
  have hz : squareVertex F 0 1 = coherentNerveVertex (dgFixedNullInput R A) := by
    have he := squareLeftEdge_target F
    let le : (dgKInputInfinity.{u, v} R).Edge (coherentNerveVertex A)
        (coherentNerveVertex (dgFixedNullInput R A)) :=
      coherentNerveEdge (dgFixedNullLeft R (A := A))
    have hle : squareLeftEdge ≫ F = SSet.yonedaEquiv.symm le.edge := hl
    rw [hle, Equiv.apply_symm_apply, le.tgt_eq] at he
    exact he.symm
  change IsZeroCategory (stableObject ((dgKInputNu R).app _ (squareVertex F 0 1)))
  rw [hz, dgKInputNu_vertex, _root_.SerrePositivity.InfinityCategories.Stable.Infinity.stableObject_vertex]
  exact dgFixedNullInput_isZeroCategory R A

lemma exists_dgOdotCertifiedNullSquare (d : DGOdotInput R) :
    ∃ F : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}) ⟶ dgKInputInfinity.{u, u + 1} R,
      squareBottomEdge ≫ F =
        SSet.yonedaEquiv.symm (coherentNerveEdge (dgOdotDiagonalInputMap R d)).edge ∧
      squareRightEdge ≫ F =
        SSet.yonedaEquiv.symm (coherentNerveEdge (dgOdotProjectionInputMap R d)).edge ∧
      squareLeftEdge ≫ F = SSet.yonedaEquiv.symm
        (coherentNerveEdge (dgFixedNullLeft R (A := dgOdotDiagonalSourceInput R d))).edge ∧
      squareTopEdge ≫ F = SSet.yonedaEquiv.symm
        (coherentNerveEdge (dgFixedNullTop R (dgOdotCompositeContracted R d))).edge ∧
      IsZeroCategory (stableObject (squareVertex (F ≫ dgKInputNu R) 0 1)) :=
  exists_dgFixedNullCertifiedSquare R (dgOdotDiagonalInputMap R d) (dgOdotProjectionInputMap R d)
    (dgOdotCompositeContracted R d) rfl

end SerrePositivity.KST.LocalizingInvariants

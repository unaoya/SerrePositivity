module
public import SerrePositivity.InfinityCategories.DGNerve.FiberBoundaryJoinFiller
public import SerrePositivity.InfinityCategories.DGNerve.SliceBoundaryFromJoinFaces

/-! # 貼合せた join 充填の全ての境界面

概要：標準 fiber の join 充填は指定された slice 境界の各面と一致する。
方針：各セルの既知の面の保存から二セルの押し出しによる外延性を使う。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：slice の直接の境界充填の最後の境界検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.InfinityCategories.DGNerve

open CategoryTheory Opposite DifferentialGraded CochainComplex HomComplex
open scoped Simplicial

variable {A : Type u} [CommRing A] {B C D : Complex A}

/-- 概要：Left 側単体の既知面を表す写像は元の境界の対応するセルに一致する。
方針：単体の面をデータの引き戻しに戻し、候補の面の保存と元の境界の回収公式を使う。
規約：HA Proposition 1.3.1.10。使われ方：join の各境界面を元の境界と比較する。 -/
lemma fiberBoundaryLeftSimplex_face_map {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (j : Fin (n + 4)) (hj : j ∈ cospanPrefixFaces n) :
    SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (fiberBoundaryLeftSimplex g h b hb) =
      cospanBoundaryLeftLift n j hj ≫ sliceOverUncurry b := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Simplex.ext
  change (fiberBoundaryLeftCandidate g h b hb).pullback j.succAboveOrderEmb.toOrderHom = _
  rw [fiberBoundaryLeftCandidate_pullback_face g h b hb j hj]
  exact cospanBoundaryLeftData_pullback_face (A := A) (D := Complex A) (n := n)
    (sliceOverUncurry b) (fun _ _ _ _ _ _ _ _ => 0) j hj

/-- 概要：Right 側単体の既知面を表す写像は元の境界の対応するセルに一致する。
方針：単体の面をデータの引き戻しに戻し、候補の面の保存と元の境界の回収公式を使う。
規約：HA Proposition 1.3.1.10。使われ方：join の各境界面を元の境界と比較する。 -/
lemma fiberBoundaryRightSimplex_face_map {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h))
    (j : Fin (n + 4)) (hj : j ∈ cospanPrefixFaces n) :
    SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (fiberBoundaryRightSimplex g h b hb) =
      cospanBoundaryRightLift n j hj ≫ sliceOverUncurry b := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Simplex.ext
  change (fiberBoundaryRightCandidate g h b hb).pullback j.succAboveOrderEmb.toOrderHom = _
  rw [fiberBoundaryRightCandidate_pullback_face g h b hb j hj]
  exact cospanBoundaryRightData_pullback_face (A := A) (D := Complex A) (n := n)
    (sliceOverUncurry b) (fun _ _ _ _ _ _ _ _ => 0) j hj

/-- 概要：貼合せた join 充填は自由因子の全ての境界面で元の slice 境界に一致する。
方針：左右のセルへの制限を比較し、二セルの押し出しによる外延性を使う。
規約：HTT §1.2.13。使われ方：join の充填を slice の境界充填へ curry する。 -/
lemma fiberBoundaryJoinFiller_faces {n : ℕ} (g : B ⟶ D) (h : C ⟶ D)
    (b : (SSet.boundary (n + 1) : SSet.{u + 1}) ⟶
      sliceOver (pullbackCospan (standardFiberSquare g h)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (standardFiberCone g h)) (j : Fin (n + 2)) :
    joinMap (SSet.stdSimplex.δ j) (𝟙 (SSet.horn 2 2 : SSet.{u + 1})) ≫
        fiberBoundaryJoinFiller g h b hb =
      joinMap (SSet.boundary.ι j) (𝟙 (SSet.horn 2 2 : SSet.{u + 1})) ≫ sliceOverUncurry b := by
  have hj : j.castAdd 2 ∈ cospanPrefixFaces n :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hidx : cospanPrefixFaceIndex (j.castAdd 2) hj = j := Fin.ext rfl
  apply (cospanJoin_isPushout n).hom_ext
  · rw [← Category.assoc, ← cospanJoinLeft_face, Category.assoc, fiberBoundaryJoinFiller_left,
      fiberBoundaryLeftSimplex_face_map g h b hb (j.castAdd 2) hj]
    simp only [cospanBoundaryLeftLift, hidx, Category.assoc]
  · rw [← Category.assoc, ← cospanJoinRight_face, Category.assoc, fiberBoundaryJoinFiller_right,
      fiberBoundaryRightSimplex_face_map g h b hb (j.castAdd 2) hj]
    simp only [cospanBoundaryRightLift, hidx, Category.assoc]

end SerrePositivity.InfinityCategories.DGNerve

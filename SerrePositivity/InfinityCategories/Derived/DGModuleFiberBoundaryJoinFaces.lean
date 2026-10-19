module
public import SerrePositivity.InfinityCategories.Derived.DGModuleFiberBoundaryJoinFiller
public import SerrePositivity.InfinityCategories.DGNerve.SliceBoundaryFromJoinFaces

/-! # 貼合せた join 充填の全ての境界面

概要：標準 fiber の join 充填は指定された slice 境界の各面と一致する。
方針：各セルの既知の面の保存から二セルの押し出しによる外延性を使う。
規約：HTT §1.2.13、HA Proposition 1.3.1.10。使われ方：slice の直接の境界充填の最後の境界検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories

open CategoryTheory Opposite DifferentialGraded DGNerve
open scoped Simplicial

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable {M N : ModuleCategory A D}

/-- 概要：Left 側単体の既知面を表す写像は元の境界の対応するセルに一致する。
方針：単体の面をデータの引き戻しに戻し、候補の面の保存と元の境界の回収公式を使う。
規約：HA Proposition 1.3.1.10。使われ方：join の各境界面を元の境界と比較する。 -/
lemma dgModuleFiberBoundaryLeftSimplex_face_map {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (j : Fin (n + 4)) (hj : j ∈ cospanPrefixFaces n) :
    SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (dgModuleFiberBoundaryLeftSimplex A D f b hb) =
      cospanBoundaryLeftLift n j hj ≫ sliceOverUncurry b := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Simplex.ext
  change (dgModuleFiberBoundaryLeftCandidate A D f b hb).pullback j.succAboveOrderEmb.toOrderHom = _
  rw [dgModuleFiberBoundaryLeftCandidate_pullback_face A D f b hb j hj]
  exact cospanBoundaryLeftData_pullback_face (A := A) (D := RightModule A D) (n := n)
    (sliceOverUncurry b) (fun _ _ _ _ _ _ _ _ => 0) j hj

/-- 概要：Right 側単体の既知面を表す写像は元の境界の対応するセルに一致する。
方針：単体の面をデータの引き戻しに戻し、候補の面の保存と元の境界の回収公式を使う。
規約：HA Proposition 1.3.1.10。使われ方：join の各境界面を元の境界と比較する。 -/
lemma dgModuleFiberBoundaryRightSimplex_face_map {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f))
    (j : Fin (n + 4)) (hj : j ∈ cospanPrefixFaces n) :
    SSet.stdSimplex.δ j ≫ SSet.yonedaEquiv.symm (dgModuleFiberBoundaryRightSimplex A D f b hb) =
      cospanBoundaryRightLift n j hj ≫ sliceOverUncurry b := by
  rw [SSet.stdSimplex.δ_comp_yonedaEquiv_symm]
  apply SSet.yonedaEquiv.injective
  rw [Equiv.apply_symm_apply]
  apply Simplex.ext
  change (dgModuleFiberBoundaryRightCandidate A D f b hb).pullback j.succAboveOrderEmb.toOrderHom
    = _
  rw [dgModuleFiberBoundaryRightCandidate_pullback_face A D f b hb j hj]
  exact cospanBoundaryRightData_pullback_face (A := A) (D := RightModule A D) (n := n)
    (sliceOverUncurry b) (fun _ _ _ _ _ _ _ _ => 0) j hj

/-- 概要：貼合せた join 充填は自由因子の全ての境界面で元の slice 境界に一致する。
方針：左右のセルへの制限を比較し、二セルの押し出しによる外延性を使う。
規約：HTT §1.2.13。使われ方：join の充填を slice の境界充填へ curry する。 -/
lemma dgModuleFiberBoundaryJoinFiller_faces {n : ℕ} (f : M ⟶ N)
    (b : (SSet.boundary (n + 1) : SSet) ⟶
      sliceOver (pullbackCospan (dgModuleFiberSquare A D f)))
    (hb : boundaryVertex n (Fin.last (n + 1)) ≫ b =
      SSet.yonedaEquiv.symm (dgModuleFiberCone A D f)) (j : Fin (n + 2)) :
    joinMap (SSet.stdSimplex.δ j) (𝟙 (SSet.horn 2 2 : SSet)) ≫
        dgModuleFiberBoundaryJoinFiller A D f b hb =
      joinMap (SSet.boundary.ι j) (𝟙 (SSet.horn 2 2 : SSet)) ≫ sliceOverUncurry b := by
  have hj : j.castAdd 2 ∈ cospanPrefixFaces n :=
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hidx : cospanPrefixFaceIndex (j.castAdd 2) hj = j := Fin.ext rfl
  apply (cospanJoin_isPushout n).hom_ext
  · rw [← Category.assoc, ← cospanJoinLeft_face, Category.assoc,
    dgModuleFiberBoundaryJoinFiller_left,
      dgModuleFiberBoundaryLeftSimplex_face_map A D f b hb (j.castAdd 2) hj]
    simp only [cospanBoundaryLeftLift, hidx, Category.assoc]
  · rw [← Category.assoc, ← cospanJoinRight_face, Category.assoc,
    dgModuleFiberBoundaryJoinFiller_right,
      dgModuleFiberBoundaryRightSimplex_face_map A D f b hb (j.castAdd 2) hj]
    simp only [cospanBoundaryRightLift, hidx, Category.assoc]

end SerrePositivity.InfinityCategories

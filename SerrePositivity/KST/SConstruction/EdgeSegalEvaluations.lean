module
public import SerrePositivity.KST.SConstruction.CutSegalNaturality

/-! # 連続する各辺への元の S 構成の制限
概要：各辺の包含と完全な評価を定義し、最初の辺と残りの区間への二分割に照合する。
方針：添字の平行移動の等号を全 gapped 図式の前合成へ移す。
規約：全高次単体での厳密等号。使われ方：全辺への Segal 射の反復加法性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet

/-- 標準区間の i 番目の連続辺の包含。 -/
def edgeIntervalInclusion (n : ℕ) (i : Fin n) : Fin (1 + 1) →o Fin (n + 1) where
  toFun j := ⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩
  monotone' _a _b h := Nat.add_le_add_left h _

/-- 元の i 番目の連続辺への完全な制限。 -/
def edgeSegalEvaluation (n : ℕ) (i : Fin n) (X : StableModel.{u}) :
    sStableModel n X ⟶ sStableModel 1 X :=
  ⟨sMap X.carrier (edgeIntervalInclusion n i),
    preservesCofiberData_sMap X.carrier (edgeIntervalInclusion n i)⟩

/-- 一辺だけの標準区間の辺評価は恒等関手。 -/
lemma edgeSegalEvaluation_one (i : Fin 1) (X : StableModel.{u}) :
    edgeSegalEvaluation 1 i X = 𝟙 (sStableModel 1 X) := by
  have hi : edgeIntervalInclusion 1 i = OrderHom.id := by
    apply DFunLike.ext
    intro j
    apply Fin.ext
    change i.val + j.val = j.val
    have := i.isLt
    omega
  apply Subtype.ext
  change sMap X.carrier (edgeIntervalInclusion 1 i) = 𝟙 _
  rw [hi, sMap_id]

/-- 一番目の切断の左評価は最初の連続辺への元の評価。 -/
lemma cutLeftSegalEvaluation_first (n : ℕ) (X : StableModel.{u}) :
    cutLeftSegalEvaluation (n + 2) ⟨1, by omega⟩ X =
      edgeSegalEvaluation (n + 2) ⟨0, by omega⟩ X := by
  have hi : cutLeftIntervalInclusion (n + 2) ⟨1, by omega⟩ =
      edgeIntervalInclusion (n + 2) ⟨0, by omega⟩ := by
    apply DFunLike.ext
    intro j
    apply Fin.ext
    exact (Nat.zero_add j.val).symm
  apply Subtype.ext
  exact congrArg (sMap X.carrier) hi

/-- 最初の辺の後の区間の各辺評価は元の次の連続辺への評価そのもの。 -/
lemma cutRightSegalEvaluation_edge (n : ℕ) (i : Fin (n + 1)) (X : StableModel.{u}) :
    cutRightSegalEvaluation (n + 2) ⟨1, by omega⟩ X ≫ edgeSegalEvaluation (n + 1) i X =
      edgeSegalEvaluation (n + 2) i.succ X := by
  have hi : (cutRightIntervalInclusion (n + 2) ⟨1, by omega⟩).comp
      (edgeIntervalInclusion (n + 1) i) = edgeIntervalInclusion (n + 2) i.succ := by
    apply DFunLike.ext
    intro j
    apply Fin.ext
    change i.val + j.val + 1 = i.val + 1 + j.val
    omega
  apply Subtype.ext
  change sMap X.carrier (cutRightIntervalInclusion (n + 2) ⟨1, by omega⟩) ≫
    sMap X.carrier (edgeIntervalInclusion (n + 1) i) = _
  rw [← sMap_comp, hi]
  rfl

end SerrePositivity.KST.SConstruction

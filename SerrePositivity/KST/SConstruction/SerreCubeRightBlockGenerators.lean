module
public import SerrePositivity.KST.SConstruction.SerreCubeRightBlockNaturalLaws

/-! # 全座標の元の生成射に関する鎖比較の右因子自然性
概要：零座標と右端保持の証明から、元の全ての面・削除・max の可換性を得る。
方針：元の座標を Fin.cases で分け、元の一段小さい生成射の右端保持を使う。
規約：全次元・全座標で追加仮定なし。使われ方：全生成語と全具体的射への拡張。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 元の全座標の面で右ブロックの連結比較は自然。 -/
lemma serreCubeRightBlockNatural_face (n m : ℕ) (b : Bool) (i : Fin (m + 1)) :
    SerreCubeRightBlockNatural A n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b m i) := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact serreCubeRightBlockNatural_face_zero A n 0 b
  | succ m ih =>
    refine Fin.cases (serreCubeRightBlockNatural_face_zero A n (m + 1) b) (fun j => ?_) i
    have h := serreCubeRightBlockNatural_keep A n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeFace b m j) (ih j)
    rw [concreteCubeRightKeepHom_face] at h
    exact h

/-- 元の全座標の削除で右ブロックの連結比較は自然。 -/
lemma serreCubeRightBlockNatural_degeneracy (n m : ℕ) (i : Fin (m + 1)) :
    SerreCubeRightBlockNatural A n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy m i) := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact serreCubeRightBlockNatural_degeneracy_zero A n 0
  | succ m ih =>
    refine Fin.cases (serreCubeRightBlockNatural_degeneracy_zero A n (m + 1)) (fun j => ?_) i
    have h := serreCubeRightBlockNatural_keep A n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeDegeneracy m j) (ih j)
    rw [concreteCubeRightKeepHom_degeneracy] at h
    exact h

/-- 元の全座標の max で右ブロックの連結比較は自然。 -/
lemma serreCubeRightBlockNatural_connection (n m : ℕ) (i : Fin (m + 1)) :
    SerreCubeRightBlockNatural A n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection m i) := by
  induction m with
  | zero =>
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact serreCubeRightBlockNatural_connection_zero A n 0
  | succ m ih =>
    refine Fin.cases (serreCubeRightBlockNatural_connection_zero A n (m + 1)) (fun j => ?_) i
    have h := serreCubeRightBlockNatural_keep A n (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.concreteCubeConnection m j) (ih j)
    rw [concreteCubeRightKeepHom_connection] at h
    exact h

end SerrePositivity.KST.SConstruction

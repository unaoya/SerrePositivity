module

public import SerrePositivity.KST.Comparison.HatGLCoefficientKan
public import SerrePositivity.KST.Comparison.MatrixZeroStabilization
public import SerrePositivity.KST.Comparison.HatGLStabilization

/-!
# ĜL の高次の係数比較の実際の射

概要：有限 rank の高次の係数表示を、単位行列を引いてから係数を取る単体写像で記述する。
方針：包含・平行移動・係数評価の誘導写像の合成則を使う。
規約：KST Lemma 2.13 の rank の自然性のために比較射を固定する。
使われ方：安定化後の係数行列の余極限の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite SSet
open scoped Simplicial

/--
概要：零次の単位の完全退化は全次数の単位である。
方針：単体的環の射の単位保存を使う。
規約：行列環にも同じ補題を適用する。
使われ方：平行移動の各次数での計算。
-/
theorem ringDegenerateVertex_one (A : SimplicialObject RingCat.{u}) (n : ℕ) :
    ringDegenerateVertex A (1 : A.obj (op ⦋0⦌)) n = 1 :=
  map_one (A.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op).hom

/--
概要：ĜL の行列から単位行列を引き、その一係数を取る単体写像。
方針：全行列への包含、単位の平行移動、係数評価を合成する。
規約：単位基点を零基点へ送る。
使われ方：高次の係数表示の標準比較射。
-/
def hatGLShiftedEntryMap (A : SimplicialObject RingCat.{u}) (r : ℕ) (i j : Fin r) :
    hatGLSpace A r ⟶ ringSpace A :=
  hatGLMatrixInclusion A r ≫
    (ringTranslationIso (matrixRingObject A r)
      (1 : Matrix (Fin r) (Fin r) (A.obj (op ⦋0⦌)))).hom ≫ matrixEntryMap A r i j

/--
概要：単位を引く係数評価の写像は単位基点を零へ送る。
方針：零次の完全退化と自己減法を計算する。
規約：K-L9 の誘導準同型の基点保存の証明。
使われ方：高次の係数表示の各成分。
-/
theorem hatGLShiftedEntryMap_basepoint (A : SimplicialObject RingCat.{u}) (r : ℕ)
    (i j : Fin r) : (hatGLShiftedEntryMap A r i j).app (op ⦋0⦌)
      (1 : hatGLSubmonoid A r 0) = (0 : A.obj (op ⦋0⦌)) := by
  let b : Matrix (Fin r) (Fin r) (A.obj (op ⦋0⦌)) :=
    ringDegenerateVertex (matrixRingObject A r) 1 0
  have hb : b = 1 := ringDegenerateVertex_zero (matrixRingObject A r) 1
  change ((1 : Matrix (Fin r) (Fin r) (A.obj (op ⦋0⦌))) - b) i j = 0
  rw [hb, sub_self]
  rfl

/--
概要：単位を引く係数写像の各次数での計算。
方針：単位の完全退化の式で平行移動を通常の自己減法に直す。
規約：行列の実際の値を保持する。
使われ方：rank の安定化後の各ブロックの計算。
-/
theorem hatGLShiftedEntryMap_app (A : SimplicialObject RingCat.{u}) (r q : ℕ)
    (a : hatGLSubmonoid A r q) (i j : Fin r) :
    (hatGLShiftedEntryMap A r i j).app (op ⦋q⦌) a = (a.val - 1) i j := by
  let b : Matrix (Fin r) (Fin r) (A.obj (op ⦋q⦌)) :=
    ringDegenerateVertex (matrixRingObject A r) 1 q
  have hb : b = 1 := ringDegenerateVertex_one (matrixRingObject A r) q
  change (a.val - b) i j = (a.val - 1) i j
  rw [hb]

/--
概要：高次の係数表示の一成分は、単位を引く係数写像の誘導準同型である。
方針：構成した三つの群同型の合成を誘導写像の合成則で計算する。
規約：単なる抽象的な群同型でなく標準射との一致を示す。
使われ方：rank の安定化との可換性。
-/
theorem hatGLCoefficientHomotopyMulEquiv_entry (A : SimplicialObject RingCat.{u})
    (r n : ℕ) (x : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (hatGLSpace A r) n (1 : hatGLSubmonoid A r 0))
    (i j : Fin r) :
    simplicialRingHatGLCoefficientHomotopyMulEquiv A r n x i j =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (hatGLShiftedEntryMap A r i j)
        (hatGLShiftedEntryMap_basepoint A r i j) x := by
  let T := (ringTranslationIso (matrixRingObject A r)
    (1 : Matrix (Fin r) (Fin r) (A.obj (op ⦋0⦌)))).hom
  let hT := ringTranslationIso_basepoint (matrixRingObject A r)
    (1 : Matrix (Fin r) (Fin r) (A.obj (op ⦋0⦌)))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (matrixEntryMap A r i j) rfl
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map T hT
      (hatGLPositiveHomotopyMulEquiv A r (1 : hatGLSubmonoid A r 0) n x)) = _
  rw [hatGLPositiveHomotopyMulEquiv_apply]
  have h₁ := DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n)
    (hatGLMatrixInclusion A r) rfl T hT hT) x
  have h₂ := DFunLike.congr_fun (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (n := n)
    (hatGLMatrixInclusion A r ≫ T) hT (matrixEntryMap A r i j) rfl
      (hatGLShiftedEntryMap_basepoint A r i j)) x
  exact (congrArg (fun z => _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (matrixEntryMap A r i j) rfl z)
    h₁.symm).trans h₂.symm

end SerrePositivity.KST.Comparison

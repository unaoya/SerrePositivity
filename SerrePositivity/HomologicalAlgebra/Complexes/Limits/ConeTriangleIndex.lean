module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Index

/-!
概要：大域評価三角形の三相の時刻を、元の cone と終端付き単体の添字へ写す。
方針：零相を始点へ、二相を終点へ送り、残りは後続・前面埋め込みを使う。
規約：全ての単調作用素との厳密な可換式を保つ。使われ方：混合単体の面・退化自然性。
-/
@[expose] public section
namespace SerrePositivity.ComplexLimits
open _root_.SerrePositivity.InfinityCategories

def coneTriangleFrontIndex {n : ℕ} (τ : Fin (n + 1) →o Fin 3) :
    Fin (n + 1) →o Fin (n + 2) where
  toFun i := if τ i = 0 then 0 else i.succ
  monotone' i j hij := by
    by_cases hi : τ i = 0
    · simp only [hi, ↓reduceIte]
      exact Fin.zero_le _
    · have hj : τ j ≠ 0 := by
        intro hj
        apply hi
        exact le_antisymm (hj ▸ τ.monotone hij) (Fin.zero_le _)
      simp only [hi, hj, ↓reduceIte]
      exact Fin.succ_le_succ_iff.mpr hij

def coneTriangleBackIndex {n : ℕ} (τ : Fin (n + 1) →o Fin 3) :
    Fin (n + 1) →o Fin (n + 2) where
  toFun i := if τ i = 2 then Fin.last (n + 1) else i.castSucc
  monotone' i j hij := by
    by_cases hj : τ j = 2
    · simp only [hj, ↓reduceIte]
      exact Fin.le_last _
    · have hi : τ i ≠ 2 := by
        intro hi
        apply hj
        have h := τ.monotone hij
        have hb := (τ j).isLt
        apply Fin.ext
        change (τ j).val = 2
        rw [hi] at h
        change 2 ≤ (τ j).val at h
        omega
      simp only [hi, hj, ↓reduceIte]
      exact Fin.castSucc_le_castSucc_iff.mpr hij

lemma coneTriangleFrontIndex_zero {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (i : Fin (n + 1)) (hi : τ i = 0) : _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ i = 0 := by
  change (if τ i = 0 then 0 else i.succ) = 0
  simp only [hi, ↓reduceIte]

lemma coneTriangleFrontIndex_ne_zero {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (i : Fin (n + 1)) (hi : τ i ≠ 0) : _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ i = i.succ := by
  change (if τ i = 0 then 0 else i.succ) = i.succ
  simp only [hi, ↓reduceIte]

lemma coneTriangleBackIndex_two {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (i : Fin (n + 1)) (hi : τ i = 2) :
    _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ i = Fin.last (n + 1) := by
  change (if τ i = 2 then Fin.last (n + 1) else i.castSucc) = Fin.last (n + 1)
  simp only [hi, ↓reduceIte]

lemma coneTriangleBackIndex_ne_two {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (i : Fin (n + 1)) (hi : τ i ≠ 2) : _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ i = i.castSucc := by
  change (if τ i = 2 then Fin.last (n + 1) else i.castSucc) = i.castSucc
  simp only [hi, ↓reduceIte]

lemma coneTriangleFrontIndex_reindex {m n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ).comp θ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ).comp (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex (τ.comp θ)) := by
  apply DFunLike.ext
  intro i
  change (if τ (θ i) = 0 then 0 else (θ i).succ) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.prependOrderHom θ (if τ (θ i) = 0 then 0 else i.succ)
  split_ifs <;> rfl

lemma coneTriangleBackIndex_reindex {m n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (θ : Fin (m + 1) →o Fin (n + 1)) :
    (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ).comp θ =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom θ).comp
        (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex (τ.comp θ)) := by
  apply DFunLike.ext
  intro i
  change (if τ (θ i) = 2 then Fin.last (n + 1) else (θ i).castSucc) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom θ
      (if τ (θ i) = 2 then Fin.last (m + 1) else i.castSucc)
  split_ifs
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_last θ).symm
  · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extendOrderHom_castSucc θ i).symm

end SerrePositivity.ComplexLimits

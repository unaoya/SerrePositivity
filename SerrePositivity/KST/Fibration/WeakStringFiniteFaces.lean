module
public import SerrePositivity.KST.Fibration.WeakStringFaceEdges
public import SerrePositivity.KST.Fibration.WeakStringTriangleAdditivity

/-! # 元の有限比較の面作用：初期頂点・保存される cofiber・合成の加法性 -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 正の面は、有限比較の元の初期頂点を厳密に保つ。 -/
lemma weakStringFiniteComparison_face_initial {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) (i : Fin (n + 1)) :
    (multiRealizationFunctor r).map (weakStringExactMap q (SimplexCategory.δ i.succ)) ≫
      weakStringFiniteComparison q n r ≫ fst _ _ =
        (multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋n + 1⦌ 0) := by
  rw [weakStringFiniteComparison_reindex_initial]
  congr 2

/-- 第零面は、初期頂点を元の第二頂点へ移す。 -/
lemma weakStringFiniteComparison_face_zero_initial {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) :
    (multiRealizationFunctor r).map (weakStringExactMap q (SimplexCategory.δ (0 : Fin (n + 2)))) ≫
      weakStringFiniteComparison q n r ≫ fst _ _ =
        (multiRealizationFunctor r).map (weakStringVertexTopExact q ⦋n + 1⦌ 1) := by
  rw [weakStringFiniteComparison_reindex_initial]
  rfl

/-- 除く頂点より前では、有限比較の元の cofiber 成分をそのまま回収する。 -/
lemma weakStringFiniteComparison_face_cofiber_before {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) (i : Fin (n + 2)) (j : Fin n) (h : j.val + 1 < i.val) :
    (multiRealizationFunctor r).map (weakStringExactMap q (SimplexCategory.δ i)) ≫
      weakStringFiniteComparison q n r ≫ snd _ _ ≫ Pi.π _ j =
        weakStringCofiberMultiMap q (consecutiveWeakStringEdge (n + 1) j.castSucc) r := by
  rw [weakStringFiniteComparison_reindex_cofiber, consecutiveWeakStringEdge_face_before n i j h]

/-- 除く頂点より後では、有限比較の元の次の cofiber 成分を回収する。 -/
lemma weakStringFiniteComparison_face_cofiber_after {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) (i : Fin (n + 2)) (j : Fin n) (h : i.val ≤ j.val) :
    (multiRealizationFunctor r).map (weakStringExactMap q (SimplexCategory.δ i)) ≫
      weakStringFiniteComparison q n r ≫ snd _ _ ≫ Pi.π _ j =
        weakStringCofiberMultiMap q (consecutiveWeakStringEdge (n + 1) j.succ) r := by
  rw [weakStringFiniteComparison_reindex_cofiber, consecutiveWeakStringEdge_face_after n i j h]

/-- 内部面で合成される一成分は、元の隣接二 cofiber 成分の K-1 加法である。 -/
theorem weakStringFiniteComparison_innerFace_addition {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n r : ℕ) (i : Fin (n + 1)) :
    AnodyneHomotopy.anodyneQ.map
      ((multiRealizationFunctor (r + 1)).map
        (weakStringExactMap q (SimplexCategory.δ i.castSucc.succ)) ≫
        weakStringFiniteComparison q (n + 1) (r + 1) ≫ snd _ _ ≫ Pi.π _ i) =
      AnodyneHomotopy.anodyneQ.map (lift
        (weakStringFiniteComparison q (n + 2) (r + 1) ≫ snd _ _ ≫ Pi.π _ i.castSucc)
        (weakStringFiniteComparison q (n + 2) (r + 1) ≫ snd _ _ ≫ Pi.π _ i.succ)) ≫
          kernelMultiAddition q r := by
  rw [weakStringFiniteComparison_reindex_cofiber, consecutiveWeakStringEdge_innerFace,
    weakStringFiniteComparison_cofiber, weakStringFiniteComparison_cofiber]
  have h := weakStringTriangleMultiAddition q (consecutiveWeakStringTriangle n i) r
  rw [weakStringCofiberMultiPair, consecutiveWeakStringTriangle_first,
    consecutiveWeakStringTriangle_second] at h
  exact h

end SerrePositivity.KST.Fibration

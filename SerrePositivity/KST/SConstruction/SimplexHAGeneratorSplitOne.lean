module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSplitRaw
public import SerrePositivity.KST.SConstruction.SimplexHATopValueRecovery

/-! # 元の内部一端点生成元の native HA 値の左右分解
概要：左右の任意の生成元の間に一端点を挿入した値を、同じ左右 HA 値の合成へ戻す。
方針：任意右側集合の生の値の分解を一点右端へ適用し、元の生成元次数へ移す。
規約：元の切断頂点・全因子・次数和を保持。使われ方：実一面の tensor 鎖射への制限。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] {D : Type v} [DGCategory A D]

/-- 元の内部一端点生成元の値は、同じ左右生成元の HA 値の元の豊穣順合成。 -/
lemma simplexHAGeneratorValue_split_one_heq {N : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D N)
    (n : ℕ) (i : SerreCubeGeneratorIndex n) (m : ℕ) (j : SerreCubeGeneratorIndex m)
    (v : Fin (n + 1 + m + 1) ↪o Fin (N + 1)) (b : Fin (N + 1))
    (hb : v (Fin.last (n + 1 + m)) < b) :
    HEq (simplexHAGeneratorValue A s (n + 1 + m)
      (serreCubeGeneratorConcat (n + 1) (i, 1) m j) v b hb)
      (forward A
        (simplexHAGeneratorValue A s n i (simplexHASplitLeft n m v)
          (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v))
        (simplexHAGeneratorValue A s m j (simplexHASplitRight n m v) b
          (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb)) rfl) := by
  have h := simplexHABeadWordDecode_split_one_rawValue A s n i m j v {b}
    (Finset.singleton_nonempty b) (fun _ hr => (Finset.mem_singleton.mp hr) ▸ hb)
  have hp := serreCubeGeneratorDegree_freeDimension n i
  have hq := serreCubeGeneratorDegree_freeDimension m j
  have hl := complexElement_degree_cast_heq A
    (homObject A D (s.obj (v 0)) (s.obj (simplexHASplitCut n m v))) hp.symm
    (simplexHABeadWordRawValue A s (simplexHAGeneratorWord n i (simplexHASplitLeft n m v)
      (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v)))
  have hr := complexElement_degree_cast_heq A
    (homObject A D (s.obj (simplexHASplitCut n m v)) (s.obj b)) hq.symm
    (simplexHABeadWordRawValue A s (simplexHAGeneratorWord m j (simplexHASplitRight n m v) b
      (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb)))
  have hc : HEq (simplexHASplitRawValue A s n i m j v {b} (Finset.singleton_nonempty b)
      (fun _ hr => (Finset.mem_singleton.mp hr) ▸ hb))
      (forward A
        (simplexHAGeneratorValue A s n i (simplexHASplitLeft n m v)
          (simplexHASplitCut n m v) (simplexHASplitLeft_last_lt n m v))
        (simplexHAGeneratorValue A s m j (simplexHASplitRight n m v) b
          (lt_of_eq_of_lt (simplexHASplitRight_last n m v) hb)) rfl) := by
    exact dgForward_heq A rfl rfl rfl hp.symm hq.symm
      (show -((serreCubeGeneratorFreeDimension n i + serreCubeGeneratorFreeDimension m j +
        ({b} : Finset (Fin (N + 1))).card - 1 : ℕ) : ℤ) =
          serreCubeGeneratorDegree n i + serreCubeGeneratorDegree m j by
            rw [Finset.card_singleton, Nat.add_sub_cancel]
            omega) _ _ _ _ _ _ hl.symm hr.symm
  exact (complexElement_degree_cast_heq A _
    (serreCubeGeneratorDegree_freeDimension (n + 1 + m)
      (serreCubeGeneratorConcat (n + 1) (i, 1) m j)).symm _).trans (h.trans hc)

end SerrePositivity.KST.SConstruction

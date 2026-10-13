module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.SetTheory.Cardinal.Order

/-! # 一般剰余体拡大の生成元の添字

K自身に任意の整列を入れるため、添字と各初期部分はKと同じ宇宙に収まる。
初期部分が生成する中間体の包含・一元追加・合併・被覆を確認する。
これは体側の図式であり、対応する環側の両立した図式の存在はまだ結論しない。
順序は生成元のラベルの順序であり、順序体構造を要求しない。
-/

public section
namespace SerrePositivity

universe u
/-- 生成元の型そのものを同じ宇宙の整列添字として使用できる。 -/
theorem exists_residueGeneratorOrder (K : Type u) :
    ∃ (_ : LinearOrder K), WellFoundedLT K := exists_wellFoundedLT K

variable (k K : Type*) [Field k] [Field K] [Algebra k K] [LinearOrder K]

/-- 元iを加える前の中間体。 -/
def residueGeneratorBefore (i : K) : IntermediateField k K :=
  IntermediateField.adjoin k (Set.Iio i)

/-- 元iを加えた後の中間体。 -/
def residueGeneratorAfter (i : K) : IntermediateField k K :=
  IntermediateField.adjoin k (Set.Iic i)

/-- 生成元を進めると中間体も増加する。 -/
theorem residueGeneratorAfter_mono : Monotone (residueGeneratorAfter k K) :=
  fun i j hij ↦ IntermediateField.adjoin.mono k (Set.Iic i) (Set.Iic j)
    (Set.Iic_subset_Iic.mpr hij)

/-- 一元を加えることで閉初期部分の中間体が得られる。 -/
theorem residueGeneratorAfter_eq_adjoin (i : K) :
    residueGeneratorAfter k K i =
      (IntermediateField.adjoin (residueGeneratorBefore k K i) {i}).restrictScalars k := by
  rw [residueGeneratorBefore, IntermediateField.adjoin_adjoin_left]
  unfold residueGeneratorAfter
  congr 1
  ext x
  simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio, Set.mem_singleton_iff]
  exact le_iff_lt_or_eq

/-- 開初期部分の中間体は、それ以前の閉初期部分の中間体の合併である。 -/
theorem residueGeneratorBefore_eq_iSup (i : K) :
    residueGeneratorBefore k K i = ⨆ j : Set.Iio i, residueGeneratorAfter k K j.val := by
  have h : (Set.Iio i : Set K) = ⋃ j : Set.Iio i, Set.Iic j.val := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, le_rfl⟩
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      exact lt_of_le_of_lt hj j.property
  unfold residueGeneratorBefore residueGeneratorAfter
  exact (congrArg (IntermediateField.adjoin k) h).trans
    (IntermediateField.adjoin_iUnion k (fun j : Set.Iio i ↦ Set.Iic j.val))

/-- 最初の生成元の前には、基底体だけがある。 -/
theorem residueGeneratorBefore_eq_bot (i : K) (hi : IsMin i) :
    residueGeneratorBefore k K i = ⊥ := by
  have h : (Set.Iio i : Set K) = ∅ := Set.eq_empty_iff_forall_notMem.mpr
    (fun _ hx ↦ hi.not_lt hx)
  unfold residueGeneratorBefore
  rw [h, IntermediateField.adjoin_empty]

/-- 各指定体の元は、その元までの中間体に入るので、図式はK全体を覆う。 -/
theorem residueGeneratorAfter_cover (x : K) :
    x ∈ residueGeneratorAfter k K x :=
  IntermediateField.subset_adjoin k (Set.Iic x) le_rfl

end SerrePositivity

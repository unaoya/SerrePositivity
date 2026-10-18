module

public import SerrePositivity.KST.Descent.SchemeFacts

/-!
# 定理 3.1 の相異なる section の一致場所

## 概要
有限個の相異なる射の等化子の像の和を閉中心とし、既約被約な基底上で真閉性を証明する。

## 方針
各等化子は閉埋め込み。点全射なら被約性により二射が等しくなるので、各像は真閉。
既約性により有限個の真閉部分の和も真閉であり、有限次元の上界から次元が下がる。

## 規約
一致場所はスキームの等化子の像であり、基礎点写像の単なる一致集合とは区別する。
補集合での一致の排除は、任意の試験スキームからの共通な制限について述べる。

## 使われ方
論文 定理 3.1 の軌道正方形で、translated section の一致場所の和 Z を作る。
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Set

namespace SerrePositivity.KST.Descent

/-- 概要：既約空間は有限個の真閉部分の和では覆えない（論文 定理 3.1）。
方針：有限閉被覆に対する既約性を用い、一つの閉部分が全体を含む矛盾を得る。
規約：添字が空の場合も含む。既約空間は非空である。
使われ方：相異なる section の有限個の一致場所の和の真閉性。 -/
theorem finite_iUnion_proper_closed {X I : Type*} [TopologicalSpace X] [IrreducibleSpace X]
    [Finite I] (Z : I → Set X) (closed : ∀ i, IsClosed (Z i))
    (proper : ∀ i, Z i ≠ univ) : (⋃ i, Z i) ≠ univ := by
  classical
  let := Fintype.ofFinite I
  let family : Finset (Set X) := Finset.univ.image Z
  have union_eq : ⋃₀ (family : Set (Set X)) = ⋃ i, Z i := by simp [family]
  intro cover
  obtain ⟨W, hW, hsub⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp (IrreducibleSpace.isIrreducible_univ X) family
      (by
        intro W hW
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hW
        exact closed i)
      (by rw [union_eq, cover])
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hW
  exact proper i (Set.eq_univ_of_univ_subset hsub)

variable {S : Scheme.{u}} {X Y : Over S} {I : Type*}

/-- 概要：異なる添字の射の等化子の像の和（論文 定理 3.1 の Z）。
方針：異なる添字の順序対を添字として、実際の等化子の像を合併する。
規約：同じ添字の対は含めず、一つしか section がない場合は空集合になる。
使われ方：軌道正方形の閉中心の台。 -/
noncomputable def coincidenceLocus (sections : I → (X ⟶ Y)) : Set X.left :=
  ⋃ pair : {p : I × I // p.1 ≠ p.2},
    Set.range (equalizer.ι (sections pair.val.1) (sections pair.val.2)).left

/-- 概要：有限族の一致場所の和は閉（論文 定理 3.1）。
方針：分離性による等化子の閉埋め込み性と、有限和の閉性を使う。
規約：射が相異なるという仮定は閉性には不要。
使われ方：一致場所の補集合を開スキームとして取る。 -/
theorem coincidenceLocus_isClosed [Finite I] [IsSeparated Y.hom]
    (sections : I → (X ⟶ Y)) : IsClosed (coincidenceLocus sections) := by
  apply isClosed_iUnion_of_finite
  intro pair
  exact (Scheme.Hom.isClosedEmbedding _).isClosed_range

/-- 概要：既約被約な始域からの有限個の相異なる射の一致場所の和は真閉（定理 3.1）。
方針：各等化子の像の真閉性と、既約空間の有限閉被覆の性質を組み合わせる。
規約：被約性は始域、分離性は終域の構造射に課す。
使われ方：translated section の一致場所を次元帰納の中心にする。 -/
theorem coincidenceLocus_ne_univ [Finite I] [IsSeparated Y.hom]
    [IsReduced X.left] [IrreducibleSpace X.left]
    (sections : I → (X ⟶ Y)) (distinct : Function.Injective sections) :
    coincidenceLocus sections ≠ univ := by
  apply finite_iUnion_proper_closed
  · intro pair
    exact (Scheme.Hom.isClosedEmbedding _).isClosed_range
  · intro pair
    exact equalizer_range_ne_univ_of_ne _ _ (distinct.ne pair.property)

/-- 概要：一致場所の外では、異なる射は同じ試験スキーム上で一致できない（定理 3.1）。
方針：共通の制限を等化子に持ち上げ、その点の像が一致場所に入る矛盾を得る。
規約：基礎点写像の一致からスキームの射の一致を推論する補題ではない。
使われ方：一致場所の補集合における section の交わりの排除。 -/
theorem eq_index_of_common_restriction_outside
    (sections : I → (X ⟶ Y)) {i j : I} {W : Over S} (v : W ⟶ X)
    (agreement : v ≫ sections i = v ≫ sections j) (w : W.left)
    (outside : v.left w ∉ coincidenceLocus sections) : i = j := by
  by_contra hne
  apply outside
  apply Set.mem_iUnion.mpr
  refine ⟨⟨(i, j), hne⟩, (equalizer.lift v agreement).left w, ?_⟩
  have h := congrArg (fun k ↦ k.left) (equalizer.lift_ι v agreement)
  exact congrArg (fun k ↦ k w) h

/-- 概要：有限な次元上界を持つ既約被約な基底では一致場所の次元が下がる（定理 3.1）。
方針：一致場所の真閉性と、真閉部分の鎖を一段伸ばす次元補題を使う。
規約：自然数 d の上界を明示する。空の一致場所は次元 ⊥ のまま扱う。
使われ方：軌道正方形の中心上の次元帰納。 -/
theorem coincidenceLocus_dimension_lt_bound [Finite I] [IsSeparated Y.hom]
    [IsReduced X.left] [IrreducibleSpace X.left]
    (sections : I → (X ⟶ Y)) (distinct : Function.Injective sections)
    (d : ℕ) (bound : topologicalKrullDim X.left ≤ d) :
    topologicalKrullDim (coincidenceLocus sections) < d :=
  topologicalKrullDim_properClosed_lt_bound _ (coincidenceLocus_isClosed sections)
    (coincidenceLocus_ne_univ sections distinct) d bound

end SerrePositivity.KST.Descent

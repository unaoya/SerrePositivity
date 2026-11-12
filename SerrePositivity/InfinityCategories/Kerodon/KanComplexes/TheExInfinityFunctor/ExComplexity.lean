module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionCut
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExUnit

/-!
# Ex の単体の有限な複雑度フィルター

概要：細分の作用素の固定点で Ex の単体をフィルターする。
方針：閾値の合成則から包含を示し、零段階を X の像と同定する。
規約：Moss 2020 Notation 24。Theorem 22 の regular pairing の前段。
使われ方：X→Ex(X) の anodyne 性の組合せ的帰納。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite

/--
概要：j_n^k の前合成で固定される Ex の単体全体。
方針：細分された標準単体からの写像の等式で定義する。
規約：Moss 2020 Notation 24 の J_n^k。
使われ方：単体の複雑度を測る有限のフィルター。
-/
def exComplexity (X : SSet.{u}) (n : SimplexCategory) (k : Fin (n.len + 1)) :
    Set ((SSet.ex.obj X).obj (op n)) :=
  {s | subdivisionCutAt n k ≫ s.down = s.down}

/--
概要：閾値を上げると固定される単体が増える。
方針：j_n^l と j_n^k の合成則を使う。
規約：Moss 2020 Notation 24 の包含 J_n^k⊆J_n^l。
使われ方：複雑度の最小の閾値を選ぶ。
-/
theorem exComplexity_mono (X : SSet.{u}) (n : SimplexCategory) :
    Monotone (exComplexity X n) := by
  intro k l hkl s hs
  change subdivisionCutAt n l ≫ s.down = s.down
  calc
    _ = subdivisionCutAt n l ≫ (subdivisionCutAt n k ≫ s.down) :=
      congrArg (fun f => subdivisionCutAt n l ≫ f) hs.symm
    _ = (subdivisionCutAt n l ≫ subdivisionCutAt n k) ≫ s.down :=
      (Category.assoc _ _ _).symm
    _ = _ := by rw [subdivisionCutAt_comp n k l hkl]; exact hs

/--
概要：最大の閾値の固定点は Ex の全単体である。
方針：最後の作用素が恒等射であることを使う。
規約：Moss 2020 Notation 24 の J_n^n=Ex(X)_n。
使われ方：各単体の複雑度が有限であること。
-/
theorem exComplexity_last (X : SSet.{u}) (n : SimplexCategory) :
    exComplexity X n (Fin.last n.len) = Set.univ := by
  ext s
  simp only [exComplexity, Set.mem_ofPred_eq, subdivisionCutAt_last, Category.id_comp,
    Set.mem_univ]

/--
概要：複雑度零の固定点は X→Ex(X) の像に等しい。
方針：最終頂点写像の切断で X の単体を復元する。
規約：Moss 2020 Notation 24 の J_n^0=j_X(X_n)。
使われ方：regular pairing で添付する単体の補集合を特定する。
-/
theorem exComplexity_zero (X : SSet.{u}) (n : SimplexCategory) :
    exComplexity X n 0 = Set.range ((exUnitAt X).app (op n)) := by
  ext s
  constructor
  · intro hs
    let f : SSet.stdSimplex.obj n ⟶ X := subdivisionVertexSectionAt n ≫ s.down
    refine ⟨SSet.yonedaEquiv f, ?_⟩
    apply ULift.ext
    change subdivisionLastVertexAt n ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv f) = s.down
    rw [Equiv.symm_apply_apply]
    dsimp only [f]
    rw [← Category.assoc, ← subdivisionCutAt_zero]
    exact hs
  · rintro ⟨x, rfl⟩
    change subdivisionCutAt n 0 ≫ (subdivisionLastVertexAt n ≫ SSet.yonedaEquiv.symm x) =
      subdivisionLastVertexAt n ≫ SSet.yonedaEquiv.symm x
    rw [← Category.assoc, subdivisionCutAt_lastVertex]

/--
概要：Ex の単体が固定される最小の閾値。
方針：最後の閾値は必ず単体を含むので、有限非空集合の最小元を取る。
規約：Moss 2020 Theorem 22 の pairing で使う k。
使われ方：型 II の単体へ付け加える単体の閾値を選ぶ。
-/
def exComplexityLevel (X : SSet.{u}) (n : SimplexCategory)
    (s : (SSet.ex.obj X).obj (op n)) : Fin (n.len + 1) := by
  classical
  exact (Finset.univ.filter (fun k => s ∈ exComplexity X n k)).min'
    ⟨Fin.last n.len, by simp [exComplexity_last]⟩

/--
概要：選んだ最小閾値で単体は固定される。
方針：最小元が元の有限集合に属することを使う。
規約：Moss 2020 Theorem 22 の複雑度の選択。
使われ方：フィルターに関する最小閾値の性質。
-/
theorem exComplexityLevel_mem (X : SSet.{u}) (n : SimplexCategory)
    (s : (SSet.ex.obj X).obj (op n)) : s ∈ exComplexity X n (exComplexityLevel X n s) := by
  classical
  have h := Finset.min'_mem (Finset.univ.filter (fun k => s ∈ exComplexity X n k))
    ⟨Fin.last n.len, by simp [exComplexity_last]⟩
  exact (Finset.mem_filter.mp h).2

/--
概要：閾値 k で固定されることは、最小閾値が k 以下であることに等しい。
方針：有限集合の最小性とフィルターの単調性を使う。
規約：Moss 2020 Theorem 22 の複雑度による帰納。
使われ方：pairing の先行関係を自然数の大小に移す。
-/
theorem exComplexityLevel_le_iff (X : SSet.{u}) (n : SimplexCategory)
    (s : (SSet.ex.obj X).obj (op n)) (k : Fin (n.len + 1)) :
    exComplexityLevel X n s ≤ k ↔ s ∈ exComplexity X n k := by
  classical
  constructor
  · intro h
    exact exComplexity_mono X n h (exComplexityLevel_mem X n s)
  · intro h
    exact Finset.min'_le _ _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact h)

/--
概要：最小閾値が零であることは元の X の単体の像であることに等しい。
方針：零段階の固定点と単位の像の既証の一致を使う。
規約：Moss 2020 Notation 24、Theorem 22。
使われ方：元の X 以外の単体では複雑度が正であること。
-/
theorem exComplexityLevel_zero_iff (X : SSet.{u}) (n : SimplexCategory)
    (s : (SSet.ex.obj X).obj (op n)) :
    exComplexityLevel X n s = 0 ↔ s ∈ Set.range ((exUnitAt X).app (op n)) := by
  rw [← exComplexity_zero]
  constructor
  · intro h
    rw [← h]
    exact exComplexityLevel_mem X n s
  · intro h
    exact le_antisymm ((exComplexityLevel_le_iff X n s 0).mpr h) (Fin.zero_le _)

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor

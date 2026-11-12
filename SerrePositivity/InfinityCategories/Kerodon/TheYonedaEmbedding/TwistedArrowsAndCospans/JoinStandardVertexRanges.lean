module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.JoinCells
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexOp

/-!
概要：標準単体の join の頂点像の左右の分解。
方針：連結した有限順序写像の像を、左右の区間に分けて計算する。
規約：標準単体の同型による頂点数の移送を明示する。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、Corollary 8.1.1.13（Tag 048H）、edgewise の延長領域の同定。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：有限順序の大きさの移送は指定頂点の像への所属を保つ。
方針：大きさの等式を消去して同じ像とする。
規約：始域の頂点数は零でもよい。
使われ方：Kerodon Remark 8.1.1.2（Tag 03JH）、連結表示と標準単体表示の照合。 -/
lemma Join.mem_range_cast_iff {p q r : ℕ} (h : p = q) (f : Fin r → Fin p) (v : Fin p) :
    Fin.cast h v ∈ Set.range (fun j ↦ Fin.cast h (f j)) ↔ v ∈ Set.range f := by
  subst q
  rfl

/-- 概要：標準 join の左頂点が単体の像に含まれることは左因子の像への所属と同値。
方針：標準単体の移送を消去し、連結写像の左区間の像の計算を使う。
規約：左頂点の番号は変えない。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、edgewise の欠ける左頂点の判定。 -/
lemma joinStdSimplexIso_mem_range_left {p q d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[p] : SSet.{u}) Δ[q] d) (v : Fin (p + 1)) :
    Fin.cast (by omega : (p + 1) + (q + 1) = p + q + 1 + 1) (v.castAdd (q + 1)) ∈
      Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso p q).hom.app (Opposite.op ⦋d⦌) s) ↔
      v ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv p s.1.val s.2.1) := by
  change Fin.cast _ (v.castAdd (q + 1)) ∈
    Set.range (fun j ↦ Fin.cast (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode p q d s j)) ↔ _
  rw [Join.mem_range_cast_iff]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_range_concat_left _ _ _ _ v

/-- 概要：標準 join の右頂点が単体の像に含まれることは右因子の像への所属と同値。
方針：標準単体の移送を消去し、連結写像の右区間の像の計算を使う。
規約：右頂点の番号には p+1 を加える。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、edgewise の欠ける右頂点の判定。 -/
lemma joinStdSimplexIso_mem_range_right {p q d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (Δ[p] : SSet.{u}) Δ[q] d) (v : Fin (q + 1)) :
    Fin.cast (by omega : (p + 1) + (q + 1) = p + q + 1 + 1) (v.natAdd (p + 1)) ∈
      Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso p q).hom.app (Opposite.op ⦋d⦌) s) ↔
      v ∈ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv q (d + 1 - s.1.val) s.2.2) := by
  change Fin.cast _ (v.natAdd (p + 1)) ∈
    Set.range (fun j ↦ Fin.cast (by omega) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdEncode p q d s j)) ↔ _
  rw [Join.mem_range_cast_iff]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.mem_range_concat_right _ _ _ _ v

/-- 概要：標準単体の補った単体が一頂点を欠く面に属することはその頂点の像からの不在。
方針：空区間を別に扱い、正次数では面の所属を各頂点で判定する。
規約：r は次数ではなく頂点数。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、join の右因子の欠落条件の照合。 -/
lemma Join.augMem_face_compl_iff {p : ℕ} (i : Fin (p + 1)) (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (Δ[p] : SSet.{u}) r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem (stdSimplex.face ({i}ᶜ)) r a ↔ i ∉ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv p r a) := by
  cases r with
  | zero =>
    constructor
    · rintro _ ⟨j, _⟩
      exact Fin.elim0 j
    · intro _
      trivial
  | succ r =>
    change a ∈ (stdSimplex.face ({i}ᶜ)).obj (Opposite.op ⦋r⦌) ↔ _
    rw [stdSimplex.mem_face_iff]
    simp only [Finset.mem_compl, Finset.mem_singleton, Set.mem_range, not_exists]
    rfl

/-- 概要：反転した面の欠落頂点は標準単体へ戻すと反転した番号の欠落になる。
方針：反転同型の各頂点の式と有限順序の反転の全単射を使う。
規約：空の左区間でも成立する。
使われ方：Kerodon Corollary 8.1.1.13（Tag 048H）、edgewise の左因子の欠落条件の照合。 -/
lemma Join.augMem_op_face_compl_iff {p : ℕ} (i : Fin (p + 1)) (r : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (Δ[p] : SSet.{u}).op r) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.Join.augMem (stdSimplex.face ({i}ᶜ)).op r a ↔
      i.rev ∉ Set.range (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv p r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (stdSimplex.opIso ⦋p⦌).hom r a)) := by
  cases r with
  | zero =>
    constructor
    · rintro _ ⟨j, _⟩
      exact Fin.elim0 j
    · intro _
      trivial
  | succ r =>
    change SSet.opObjEquiv a ∈ (stdSimplex.face ({i}ᶜ)).obj (Opposite.op ⦋r⦌) ↔ _
    rw [stdSimplex.mem_face_iff]
    simp only [Finset.mem_compl, Finset.mem_singleton]
    change (∀ j : Fin (r + 1), (SSet.opObjEquiv a) j ≠ i) ↔
      ¬ ∃ j : Fin (r + 1), ((SSet.opObjEquiv a) j.rev).rev = i.rev
    constructor
    · intro h ⟨j, hj⟩
      have he := congrArg Fin.rev hj
      exact h j.rev (by simpa only [Fin.rev_rev] using he)
    · intro h j hj
      apply h
      refine ⟨j.rev, ?_⟩
      rw [Fin.rev_rev, hj]

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

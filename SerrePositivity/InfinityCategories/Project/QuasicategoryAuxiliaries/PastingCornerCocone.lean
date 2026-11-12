module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.LastJoinEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PastingCorner

/-! # 部分長方形の終端角への余錐

概要：五頂点図式の右に点を加えた join から長方形へ、終端角を頂点とする余錐を構成する。
方針：二つの座標で標準単体の最後の頂点への join の評価を使う。
規約：左因子は五頂点図式、右因子は右上の終端角。
使われ方：S4 の長方形全体の join 表示。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：空次数も許した五頂点図式の横座標の順序写像。
方針：包含と第一射影による補った単体の像を読む。
規約：ℓ は頂点数。使われ方：join の切断前の座標の計算。 -/
def pastingAugX (ℓ : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) ℓ) : Fin ℓ →o Fin 3 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 2 ℓ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ fst Δ[2] Δ[1]) ℓ s)

/-- 概要：空次数も許した五頂点図式の縦座標の順序写像。
方針：包含と第二射影による補った単体の像を読む。
規約：ℓ は頂点数。使われ方：join の切断前の座標の計算。 -/
def pastingAugY (ℓ : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) ℓ) : Fin ℓ →o Fin 2 :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 1 ℓ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augHom (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ snd Δ[2] Δ[1]) ℓ s)

/-- 概要：補った部分図式の全頂点は終端角以外である。
方針：空次数は空の添字、それ以外は部分複体の所属条件を使う。
規約：横座標二なら縦座標は一でない。
使われ方：余錐の単体から join の切断を復元する。 -/
lemma pastingAug_not_terminal (ℓ : ℕ) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augObj (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) ℓ)
    (i : Fin ℓ) : pastingAugX ℓ s i = 2 → pastingAugY ℓ s i ≠ 1 := by
  cases ℓ with
  | zero => exact Fin.elim0 i
  | succ ℓ => exact s.property i

/-- 概要：五頂点図式から終端角への余錐を長方形に写す射。
方針：各座標で右に付けた点を最後の頂点へ送り、直積へ束ねる。
規約：長方形は Δ[2] × Δ[1]。
使われ方：S4 の長方形の join 表示の順方向。 -/
def pastingCornerCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) Δ[0] ⟶ (Δ[2] : SSet.{u}) ⊗ Δ[1] :=
  lift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ fst Δ[2] Δ[1]) (𝟙 Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 2)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι ≫ snd Δ[2] Δ[1]) (𝟙 Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation 1)

/-- 概要：余錐は基底の五頂点図式をそのまま含める。
方針：直積の各射影で比較し、左因子上の join の評価を使う。
規約：射の厳密な等式。
使われ方：余錐の固定図式条件。 -/
lemma pastingCornerCocone_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) Δ[0] ≫ pastingCornerCocone = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner.ι := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [pastingCornerCocone, Category.assoc, lift_fst]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_inl,
      Category.comp_id]
  · simp only [pastingCornerCocone, Category.assoc, lift_snd]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_inl,
      Category.comp_id]

/-- 概要：切断前の余錐の横座標は元の部分図式の横座標。
方針：左因子に沿う join の評価の式を使う。
規約：i は切断より前。使われ方：余錐の単射性と全射性。 -/
lemma pastingCornerCocone_appX_of_lt {d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) Δ[0] d)
    (i : Fin (d + 1)) (hi : i.val < s.1.val) :
    (pastingCornerCocone.app (Opposite.op ⦋d⦌) s).1 i =
      pastingAugX s.1.val s.2.1 ⟨i.val, hi⟩ := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_app_of_lt 2 d _ i hi

/-- 概要：切断前の余錐の縦座標は元の部分図式の縦座標。
方針：左因子に沿う join の評価の式を使う。
規約：i は切断より前。使われ方：余錐の単射性と全射性。 -/
lemma pastingCornerCocone_appY_of_lt {d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) Δ[0] d)
    (i : Fin (d + 1)) (hi : i.val < s.1.val) :
    (pastingCornerCocone.app (Opposite.op ⦋d⦌) s).2 i =
      pastingAugY s.1.val s.2.1 ⟨i.val, hi⟩ := by
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_app_of_lt 1 d _ i hi

/-- 概要：切断以降の全頂点は長方形の終端角となる。
方針：右因子に沿う join の評価の式を各座標に使う。
規約：終端角は (2,1)。使われ方：join の切断の復元。 -/
lemma pastingCornerCocone_app_of_ge {d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) Δ[0] d)
    (i : Fin (d + 1)) (hi : s.1.val ≤ i.val) :
    (pastingCornerCocone.app (Opposite.op ⦋d⦌) s).1 i = 2 ∧
      (pastingCornerCocone.app (Opposite.op ⦋d⦌) s).2 i = 1 := by
  exact ⟨_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_app_of_ge 2 d _ i hi,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.stableLastJoinEvaluation_app_of_ge 1 d _ i hi⟩

/-- 概要：余錐の頂点が終端角以外であることは切断より前であることと同値。
方針：切断前の部分図式の所属条件と、切断以降の終端角の式を合わせる。
規約：終端角以外という条件は部分複体の定義と同じ形で書く。
使われ方：join の単体から切断位置を一意に復元する。 -/
lemma pastingCornerCocone_vertex_corner_iff {d : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingCorner : SSet.{u}) Δ[0] d) (i : Fin (d + 1)) :
    ((pastingCornerCocone.app (Opposite.op ⦋d⦌) s).1 i = 2 →
      (pastingCornerCocone.app (Opposite.op ⦋d⦌) s).2 i ≠ 1) ↔ i.val < s.1.val := by
  by_cases hi : i.val < s.1.val
  · rw [pastingCornerCocone_appX_of_lt s i hi, pastingCornerCocone_appY_of_lt s i hi]
    exact iff_of_true (pastingAug_not_terminal _ _ _) hi
  · obtain ⟨hx, hy⟩ := pastingCornerCocone_app_of_ge s i (Nat.le_of_not_gt hi)
    rw [hx, hy]
    simp only [ne_eq, not_true_eq_false, imp_false, false_iff]
    exact hi

/-- 概要：長方形への余錐の射は全次数で単射。
方針：終端角以外の頂点の位置から切断を復元し、前半の二座標と後半の一点の一意性で各因子を復元する。
規約：自然性は既に二座標の構成から得ている。
使われ方：長方形の join 同型の単射側。 -/
lemma pastingCornerCocone_app_injective (d : ℕ) :
    Function.Injective (pastingCornerCocone.{u}.app (Opposite.op ⦋d⦌)) := by
  intro s t h
  have hc : s.1 = t.1 := Fin.ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (n := d + 1)
    (by have hs : s.1.val < d + 2 := s.1.isLt; omega)
    (by have ht : t.1.val < d + 2 := t.1.isLt; omega) (by
      intro i
      rw [← pastingCornerCocone_vertex_corner_iff s i,
        ← pastingCornerCocone_vertex_corner_iff t i, h]))
  rcases s with ⟨ℓ, x, y⟩
  rcases t with ⟨ℓ', x', y'⟩
  dsimp only at hc
  subst ℓ'
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex.ext _ _ rfl ?_ ?_
  · change x = x'
    rcases ℓ with ⟨_ | k, hk⟩
    · exact @Subsingleton.elim PUnit inferInstance x x'
    · change k + 1 < d + 2 at hk
      apply Subtype.ext
      apply Prod.ext
      · apply stdSimplex.ext
        intro j
        let i : Fin (d + 1) := ⟨j.val, by have := j.isLt; omega⟩
        have he := congrArg (fun z : ((Δ[2] : SSet.{u}) ⊗ Δ[1]) _⦋d⦌ ↦ z.1 i) h
        rw [pastingCornerCocone_appX_of_lt _ i j.isLt,
          pastingCornerCocone_appX_of_lt _ i j.isLt] at he
        exact he
      · apply stdSimplex.ext
        intro j
        let i : Fin (d + 1) := ⟨j.val, by have := j.isLt; omega⟩
        have he := congrArg (fun z : ((Δ[2] : SSet.{u}) ⊗ Δ[1]) _⦋d⦌ ↦ z.2 i) h
        rw [pastingCornerCocone_appY_of_lt _ i j.isLt,
          pastingCornerCocone_appY_of_lt _ i j.isLt] at he
        exact he
  · change y = y'
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.stdAugEquiv 0 _).injective
    apply DFunLike.ext
    intro i
    exact (by decide : ∀ a b : Fin 1, a = b) _ _

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

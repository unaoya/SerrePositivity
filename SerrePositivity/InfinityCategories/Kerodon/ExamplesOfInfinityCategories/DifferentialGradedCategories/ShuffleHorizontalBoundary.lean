module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleHorizontalFaceIndex
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleDelete

/-!
# shuffle の水平境界添字の復元

概要：各因子の面から作った水平境界項が、元の面番号と水平境界の種類を保持することを示す。
方針：水平ステップの順位と挿入直後の第一座標を比較する。
規約：KST Construction A.5、先頭・末尾・内部の水平境界を含む。
使われ方：水平境界添字の同値と実境界和の並べ替え。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory
open scoped Simplicial

/-- 概要：水平ステップの列挙番号と位置の一致は第一座標で検出できる。
方針：列挙の順序同型の逆と順位の濃度公式を使う。
規約：KST A.5。使われ方：内部の面番号から元の水平ステップを復元する。 -/
lemma ShuffleIndex.horizontalStep_eq_iff {p n : ℕ} (s : ShuffleIndex p n)
    (i : Fin p) (a : Fin n) (ha : a ∈ s.val) :
    s.horizontalStep i = a ↔ (i : ℕ) = (s.left.toOrderHom a.castSucc : ℕ) := by
  constructor
  · intro he
    rw [← he, s.horizontalStep_left]
  · intro he
    let e := s.val.orderIsoOfFin s.property
    have hr := s.rank_eq_left ⟨a, ha⟩
    change (e.symm ⟨a, ha⟩ : ℕ) = (s.left.toOrderHom a.castSucc : ℕ) at hr
    have hi : i = e.symm ⟨a, ha⟩ := Fin.ext (he.trans hr.symm)
    rw [hi]
    change (e (e.symm ⟨a, ha⟩)).val = a
    exact congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)

/-- 概要：水平ステップ直前の第一座標は p より小さい。
方針：次の頂点で一つ増えた座標が p 以下であることを使う。
規約：KST A.5。使われ方：内部の面番号が最後の面でないことの確認。 -/
lemma ShuffleIndex.left_lt_of_mem {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin n) (ha : a ∈ s.val) : (s.left.toOrderHom a.castSucc : ℕ) < p := by
  have hs := s.left_step a
  rw [ite_eq_left ha] at hs
  have hb : (s.left.toOrderHom a.succ : ℕ) < p + 1 := (s.left.toOrderHom a.succ).isLt
  omega

/-- 概要：元の水平ステップから作る内部の面は、同じ挿入位置と頂点を復元する。
方針：第一座標の順位から水平ステップの列挙を逆にたどる。
規約：KST A.5。使われ方：水平境界添字の逆対応。 -/
lemma ShuffleIndex.horizontalFace_internal_coordinates {p n : ℕ} (s : ShuffleIndex p n)
    (a : Fin n) (ha : a ∈ s.val) :
    s.horizontalFacePosition (s.left.toOrderHom a.castSucc).succ = a.castSucc ∧
      s.horizontalFaceVertex (s.left.toOrderHom a.castSucc).succ = a.castSucc.succ := by
  let i := (s.left.toOrderHom a.castSucc).succ
  have h₀ : i ≠ 0 := by intro h; have := congrArg Fin.val h; dsimp [i] at this; omega
  have h₁ : i ≠ Fin.last (p + 1) := by
    intro h
    have he := congrArg Fin.val h
    have hl := s.left_lt_of_mem a ha
    change (s.left.toOrderHom a.castSucc : ℕ) + 1 = p + 1 at he
    omega
  have hs : s.horizontalStep (horizontalFaceInteriorRank i h₀ h₁) = a := by
    apply (s.horizontalStep_eq_iff _ a ha).mpr
    change ((s.left.toOrderHom a.castSucc : ℕ) + 1) - 1 = (s.left.toOrderHom a.castSucc : ℕ)
    omega
  have hp : s.horizontalFacePosition i = a.castSucc := by
    simp only [ShuffleIndex.horizontalFacePosition, dite_eq_right h₀, dite_eq_right h₁, hs]
  constructor
  · exact hp
  · change s.horizontalFaceVertex i = a.castSucc.succ
    simp only [ShuffleIndex.horizontalFaceVertex, ite_eq_right h₀, ite_eq_right h₁, hp]

/-- 概要：第一因子の面から作った水平境界項の第一座標は元の面番号。
方針：端点では始点・終点、内部では挿入した水平ステップ直後の増加を使う。
規約：KST A.5。使われ方：水平境界の対応の面番号の左逆。 -/
lemma ShuffleIndex.horizontalFace_coface {p n : ℕ} (s : ShuffleIndex p n) (i : Fin (p + 2)) :
    (s.insertHorizontal (s.horizontalFacePosition i)).left.toOrderHom (s.horizontalFaceVertex i) = i := by
  by_cases h₀ : i = 0
  · subst i
    have ht : (s.insertHorizontal 0).left.toOrderHom 0 = 0 := Fin.ext (s.insertHorizontal 0).left_zero
    simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_left rfl, dite_eq_left rfl,
      ite_true, dite_true] using ht
  · by_cases h₁ : i = Fin.last (p + 1)
    · subst i
      have ht : (s.insertHorizontal (Fin.last n)).left.toOrderHom (Fin.last (n + 1)) =
          Fin.last (p + 1) := Fin.ext (s.insertHorizontal (Fin.last n)).left_last
      simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true] using ht
    · let r := horizontalFaceInteriorRank i h₀ h₁
      let a := s.horizontalStep r
      have hstep := (s.insertHorizontal a.castSucc).left_step a.castSucc
      rw [ite_eq_left (s.insertHorizontal_mem a.castSucc)] at hstep
      have hpre := s.insertHorizontal_left a.castSucc a.castSucc
      simp only [Fin.succAbove_succ_self, lt_self_iff_false, ite_false, add_zero] at hpre
      rw [hpre] at hstep
      have hface := congrArg Fin.val (s.horizontalFaceInterior_coface i h₀ h₁)
      have ht : (s.insertHorizontal a.castSucc).left.toOrderHom a.castSucc.succ = i :=
        Fin.ext (hstep.trans hface)
      simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_right h₁, dite_eq_right h₁] using ht

/-- 概要：水平境界に属する shuffle と面の条件。
方針：先頭水平、末尾水平、内部の二つの水平ステップの三種類を列挙する。
規約：KST A.5、全ステップ数 n+1。
使われ方：全境界添字から純粋な水平部分を取り出す。 -/
def IsHorizontalShuffleFace {p n : ℕ} (s : ShuffleIndex p (n + 1)) (k : Fin (n + 2)) : Prop :=
  (k = 0 ∧ (0 : Fin (n + 1)) ∈ s.val) ∨
    (k = Fin.last (n + 1) ∧ Fin.last n ∈ s.val) ∨
      ∃ a : Fin n, k = a.castSucc.succ ∧ a.castSucc ∈ s.val ∧ a.succ ∈ s.val

/-- 概要：第一因子の各面から構成した境界項は純粋な水平境界に属する。
方針：端点と、元の水平ステップの隣への挿入の三種類を確認する。
規約：KST A.5。使われ方：水平境界添字への写像の値域の確認。 -/
lemma ShuffleIndex.horizontalFace_isHorizontal {p n : ℕ} (s : ShuffleIndex p n)
    (i : Fin (p + 2)) :
    IsHorizontalShuffleFace (s.insertHorizontal (s.horizontalFacePosition i)) (s.horizontalFaceVertex i) := by
  by_cases h₀ : i = 0
  · subst i
    have ht : IsHorizontalShuffleFace (s.insertHorizontal 0) 0 :=
      Or.inl ⟨rfl, s.insertHorizontal_mem 0⟩
    simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_left rfl, dite_eq_left rfl,
      ite_true, dite_true] using ht
  · by_cases h₁ : i = Fin.last (p + 1)
    · subst i
      have ht : IsHorizontalShuffleFace (s.insertHorizontal (Fin.last n)) (Fin.last (n + 1)) :=
        Or.inr (Or.inl ⟨rfl, s.insertHorizontal_mem (Fin.last n)⟩)
      simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true] using ht
    · let a := s.horizontalStep (horizontalFaceInteriorRank i h₀ h₁)
      have ha : a ∈ s.val := s.horizontalStep_mem _
      have hn : a.succ ∈ (s.insertHorizontal a.castSucc).val := by
        have ht := (s.insertHorizontal_mem_image a.castSucc a).mpr ha
        simpa only [Fin.succAbove_castSucc_self] using ht
      have ht : IsHorizontalShuffleFace (s.insertHorizontal a.castSucc) a.castSucc.succ :=
        Or.inr (Or.inr ⟨a, rfl, s.insertHorizontal_mem a.castSucc, hn⟩)
      simpa only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_right h₁, dite_eq_right h₁] using ht

/-- 概要：境界頂点の直前のステップ位置。最初の頂点では零番目を選ぶ。
方針：頂点番号から一つ引く切り捨て差を使う。
規約：KST A.5。使われ方：水平境界から一ステップ削除へ戻す。 -/
def shuffleBoundaryRemovalPosition {n : ℕ} (k : Fin (n + 2)) : Fin (n + 1) :=
  ⟨(k : ℕ) - 1, by have := k.isLt; omega⟩

/-- 概要：最初の境界頂点の削除位置は零。
方針：切り捨て差を計算する。規約：KST A.5。
使われ方：先頭の水平境界の逆対応。 -/
@[simp] lemma shuffleBoundaryRemovalPosition_zero (n : ℕ) :
    shuffleBoundaryRemovalPosition (0 : Fin (n + 2)) = 0 := rfl

/-- 概要：最後の境界頂点の削除位置は末尾ステップ。
方針：n+1−1=n を使う。規約：KST A.5。
使われ方：末尾の水平境界の逆対応。 -/
@[simp] lemma shuffleBoundaryRemovalPosition_last (n : ℕ) :
    shuffleBoundaryRemovalPosition (Fin.last (n + 1)) = Fin.last n := by
  apply Fin.ext
  change n + 1 - 1 = n
  omega

/-- 概要：ステップ直後の境界頂点から元のステップ位置が戻る。
方針：a+1−1=a を使う。規約：KST A.5。
使われ方：内部の水平境界の逆対応。 -/
@[simp] lemma shuffleBoundaryRemovalPosition_succ {n : ℕ} (a : Fin (n + 1)) :
    shuffleBoundaryRemovalPosition a.succ = a := by
  apply Fin.ext
  change (a : ℕ) + 1 - 1 = (a : ℕ)
  omega

/-- 概要：水平境界を作った頂点から元の挿入位置が復元される。
方針：最初・最後・内部の三つの場合に標準位置の公式を適用する。
規約：KST A.5。使われ方：水平境界の対応の位置の左逆。 -/
lemma ShuffleIndex.horizontalFace_removalPosition {p n : ℕ} (s : ShuffleIndex p n)
    (i : Fin (p + 2)) :
    shuffleBoundaryRemovalPosition (s.horizontalFaceVertex i) = s.horizontalFacePosition i := by
  by_cases h₀ : i = 0
  · subst i
    simp only [horizontalFaceVertex, horizontalFacePosition, ite_eq_left rfl, dite_eq_left rfl,
      ite_true, dite_true, shuffleBoundaryRemovalPosition_zero]
  · by_cases h₁ : i = Fin.last (p + 1)
    · subst i
      simp only [horizontalFaceVertex, horizontalFacePosition, ite_eq_right h₀, dite_eq_right h₀,
        ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true, shuffleBoundaryRemovalPosition_last]
    · rw [horizontalFaceVertex, ite_eq_right h₀, ite_eq_right h₁, shuffleBoundaryRemovalPosition_succ]

/-- 概要：水平境界の削除位置には水平ステップがある。
方針：先頭・末尾・二つの水平ステップの三つの定義の場合を調べる。
規約：KST A.5。使われ方：逆対応で水平削除を適用するための条件。 -/
lemma horizontalShuffleFace_prev_mem {p n : ℕ} (s : ShuffleIndex p (n + 1))
    (k : Fin (n + 2)) (hk : IsHorizontalShuffleFace s k) :
    shuffleBoundaryRemovalPosition k ∈ s.val := by
  rcases hk with ⟨rfl, hm⟩ | ⟨rfl, hm⟩ | ⟨a, rfl, hm, _⟩
  · simpa only [shuffleBoundaryRemovalPosition_zero] using hm
  · simpa only [shuffleBoundaryRemovalPosition_last] using hm
  · simpa only [shuffleBoundaryRemovalPosition_succ] using hm

/-- 概要：最後の面を指定すると挿入位置と頂点は二つの末尾になる。
方針：最後の面が零番目ではないことと二つの定義を使う。
規約：KST A.5。使われ方：末尾水平境界の復元。 -/
lemma ShuffleIndex.horizontalFace_last_coordinates {p n : ℕ} (s : ShuffleIndex p n) :
    s.horizontalFacePosition (Fin.last (p + 1)) = Fin.last n ∧
      s.horizontalFaceVertex (Fin.last (p + 1)) = Fin.last (n + 1) := by
  have h₀ : (Fin.last (p + 1) : Fin (p + 2)) ≠ 0 := by
    intro h
    have he := congrArg Fin.val h
    change p + 1 = 0 at he
    omega
  constructor <;> simp only [horizontalFacePosition, horizontalFaceVertex, ite_eq_right h₀,
    dite_eq_right h₀, ite_eq_left rfl, dite_eq_left rfl, ite_true, dite_true]

/-- 概要：純粋水平境界を削除して得た小さい shuffle と面番号から元の位置と頂点が復元される。
方針：端点を直接確認し、内部では削除後にも隣のステップが水平であることを使う。
規約：KST A.5、面番号は元の第一座標。
使われ方：水平境界添字の同値の右逆。 -/
lemma horizontalShuffleBoundary_recover {p n : ℕ} (s : ShuffleIndex (p + 1) (n + 1))
    (k : Fin (n + 2)) (hk : IsHorizontalShuffleFace s k) :
    let t := s.removeHorizontal (shuffleBoundaryRemovalPosition k) (horizontalShuffleFace_prev_mem s k hk)
    t.horizontalFacePosition (s.left.toOrderHom k) = shuffleBoundaryRemovalPosition k ∧
      t.horizontalFaceVertex (s.left.toOrderHom k) = k := by
  let a := shuffleBoundaryRemovalPosition k
  let ha := horizontalShuffleFace_prev_mem s k hk
  let t := s.removeHorizontal a ha
  change t.horizontalFacePosition (s.left.toOrderHom k) = a ∧
    t.horizontalFaceVertex (s.left.toOrderHom k) = k
  rcases hk with ⟨rfl, hm⟩ | ⟨rfl, hm⟩ | ⟨b, rfl, hm, hn⟩
  · have hi : s.left.toOrderHom 0 = 0 := Fin.ext s.left_zero
    rw [hi]
    exact ⟨rfl, rfl⟩
  · have hi : s.left.toOrderHom (Fin.last (n + 1)) = Fin.last (p + 1) := Fin.ext s.left_last
    rw [hi]
    simpa only [a, shuffleBoundaryRemovalPosition_last] using t.horizontalFace_last_coordinates
  · have hb : b ∈ t.val := by
      change b ∈ (s.removeHorizontal a ha).val
      rw [ShuffleIndex.removeHorizontal_mem]
      change b.castSucc.succAbove b ∈ s.val
      rw [Fin.succAbove_castSucc_self]
      exact hn
    have hr : t.insertHorizontal b.castSucc = s := by
      have ht := s.insertHorizontal_removeHorizontal a ha
      change t.insertHorizontal a = s at ht
      simpa only [a, shuffleBoundaryRemovalPosition_succ] using ht
    have hc := t.horizontalFace_internal_coordinates b hb
    have hi := t.horizontalFace_coface (t.left.toOrderHom b.castSucc).succ
    rw [hc.1, hc.2, hr] at hi
    rw [hi]
    exact hc

/-- 概要：全ての純粋水平境界の有限な添字型。
方針：大きい shuffle と頂点の対を水平境界条件で制限する。
規約：KST A.5。使われ方：水平境界の有限和の添字変換。 -/
abbrev HorizontalShuffleBoundaryIndex (p n : ℕ) :=
  {z : ShuffleIndex (p + 1) (n + 1) × Fin (n + 2) // IsHorizontalShuffleFace z.1 z.2}

/-- 概要：小さい shuffle と第一因子の面番号は全ての純粋水平境界に同値。
方針：面番号による挿入と、境界の直前の水平削除を互いの逆にする。
規約：KST Construction A.5、端点・内部を全て含む実同値。
使われ方：shuffle の水平境界和と第一因子の通常境界和の並べ替え。 -/
def horizontalShuffleBoundaryEquiv (p n : ℕ) :
    (ShuffleIndex p n × Fin (p + 2)) ≃ HorizontalShuffleBoundaryIndex p n where
  toFun z := ⟨(z.1.insertHorizontal (z.1.horizontalFacePosition z.2), z.1.horizontalFaceVertex z.2),
    z.1.horizontalFace_isHorizontal z.2⟩
  invFun z :=
    (z.val.1.removeHorizontal (shuffleBoundaryRemovalPosition z.val.2)
      (horizontalShuffleFace_prev_mem z.val.1 z.val.2 z.property),
      z.val.1.left.toOrderHom z.val.2)
  left_inv z := by
    rcases z with ⟨s, i⟩
    apply Prod.ext
    · change (s.insertHorizontal (s.horizontalFacePosition i)).removeHorizontal
        (shuffleBoundaryRemovalPosition (s.horizontalFaceVertex i)) (by
          rw [s.horizontalFace_removalPosition]
          exact s.insertHorizontal_mem _) = s
      simpa only [s.horizontalFace_removalPosition] using
        s.removeHorizontal_insertHorizontal (s.horizontalFacePosition i)
    · exact s.horizontalFace_coface i
  right_inv z := by
    rcases z with ⟨⟨s, k⟩, hk⟩
    have hr := horizontalShuffleBoundary_recover s k hk
    apply Subtype.ext
    apply Prod.ext
    · change (s.removeHorizontal (shuffleBoundaryRemovalPosition k)
        (horizontalShuffleFace_prev_mem s k hk)).insertHorizontal
        ((s.removeHorizontal (shuffleBoundaryRemovalPosition k)
          (horizontalShuffleFace_prev_mem s k hk)).horizontalFacePosition (s.left.toOrderHom k)) = s
      rw [hr.1]
      exact s.insertHorizontal_removeHorizontal _ _
    · exact hr.2

/-- 概要：水平境界の条件は有限なステップの所属から判定できる。
方針：三種類の定義を開き、有限の存在量化の決定性を使う。
規約：KST A.5。使われ方：水平境界添字型の有限集合の構成。 -/
instance horizontalShuffleFace_decidable {p n : ℕ} (s : ShuffleIndex p (n + 1))
    (k : Fin (n + 2)) : Decidable (IsHorizontalShuffleFace s k) := by
  unfold IsHorizontalShuffleFace
  infer_instance

/-- 概要：純粋水平境界の和は小さい shuffle と第一因子の面の二重和へ移せる。
方針：挿入と削除から構成した実同値に沿って有限和を移す。
規約：KST Construction A.5、任意の可換加法モノイドの項に成立。
使われ方：実 shuffle の水平境界和と第一因子の通常境界和の比較。 -/
lemma horizontalShuffleBoundary_sum {A : Type*} [AddCommMonoid A] (p n : ℕ)
    (F : HorizontalShuffleBoundaryIndex p n → A) :
    ∑ z : HorizontalShuffleBoundaryIndex p n, F z =
      ∑ s : ShuffleIndex p n, ∑ i : Fin (p + 2), F (horizontalShuffleBoundaryEquiv p n (s, i)) := by
  have ht := Fintype.sum_equiv (horizontalShuffleBoundaryEquiv p n)
    (fun z ↦ F (horizontalShuffleBoundaryEquiv p n z)) F (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type] using ht.symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories



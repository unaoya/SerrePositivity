module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleHorizontalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ShuffleMixedSum

/-!
# shuffle の全境界の水平・垂直・混合への分類

概要：端点と内部の隣接ステップの種類で全ての境界添字を三つの互いに素な部分へ分ける。
方針：二つの同種ステップと、異種ステップの交換対の分類を有限な条件で表す。
規約：KST Construction A.5、全ステップ数 n+1 は少なくとも1。
使われ方：全混合境界和の消滅と二つの純粋境界和を合成する。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

/-- 概要：指定された種類のステップだけを通る境界の条件。
方針：最初・最後・内部の隣接する二ステップを列挙する。
規約：KST A.5。使われ方：水平・垂直の同じ分類の論理部分。 -/
def IsUniformShuffleFace {n : ℕ} (P : Fin (n + 1) → Prop) (k : Fin (n + 2)) : Prop :=
  (k = 0 ∧ P 0) ∨ (k = Fin.last (n + 1) ∧ P (Fin.last n)) ∨
    ∃ a : Fin n, k = a.castSucc.succ ∧ P a.castSucc ∧ P a.succ

/-- 概要：最初の面の種類は最初のステップの種類。
方針：最後と内部の頂点は零番目でない。
規約：KST A.5。使われ方：端点の分類。 -/
lemma uniformShuffleFace_zero {n : ℕ} (P : Fin (n + 1) → Prop) :
    IsUniformShuffleFace P 0 ↔ P 0 := by
  constructor
  · rintro (⟨_, h⟩ | ⟨he, _⟩ | ⟨a, he, _, _⟩)
    · exact h
    · have hn := congrArg Fin.val he
      change 0 = n + 1 at hn
      omega
    · have hn := congrArg Fin.val he
      change 0 = (a : ℕ) + 1 at hn
      omega
  · intro h
    exact Or.inl ⟨rfl, h⟩

/-- 概要：最後の面の種類は最後のステップの種類。
方針：最初と内部の頂点は最後の頂点でない。
規約：KST A.5。使われ方：端点の分類。 -/
lemma uniformShuffleFace_last {n : ℕ} (P : Fin (n + 1) → Prop) :
    IsUniformShuffleFace P (Fin.last (n + 1)) ↔ P (Fin.last n) := by
  constructor
  · rintro (⟨he, _⟩ | ⟨_, h⟩ | ⟨a, he, _, _⟩)
    · have hn := congrArg Fin.val he
      change n + 1 = 0 at hn
      omega
    · exact h
    · have hn := congrArg Fin.val he
      change n + 1 = (a : ℕ) + 1 at hn
      have ha := a.isLt
      omega
  · intro h
    exact Or.inr (Or.inl ⟨rfl, h⟩)

/-- 概要：内部の面の種類は両隣のステップが指定種類であること。
方針：端点を除き、同じ内部頂点の番号から同じステップを復元する。
規約：KST A.5。使われ方：水平・垂直・混合の三分。 -/
lemma uniformShuffleFace_internal {n : ℕ} (P : Fin (n + 1) → Prop) (a : Fin n) :
    IsUniformShuffleFace P a.castSucc.succ ↔ P a.castSucc ∧ P a.succ := by
  constructor
  · rintro (⟨he, _⟩ | ⟨he, _⟩ | ⟨b, he, hp, hq⟩)
    · have hn := congrArg Fin.val he
      change (a : ℕ) + 1 = 0 at hn
      omega
    · have hn := congrArg Fin.val he
      change (a : ℕ) + 1 = n + 1 at hn
      have ha := a.isLt
      omega
    · have hab : a = b := by
        apply Fin.ext
        have hn := congrArg Fin.val he
        change (a : ℕ) + 1 = (b : ℕ) + 1 at hn
        omega
      subst b
      exact ⟨hp, hq⟩
  · rintro ⟨hp, hq⟩
    exact Or.inr (Or.inr ⟨a, rfl, hp, hq⟩)

/-- 概要：全てのステップが垂直である純粋境界の条件。
方針：水平集合への非所属を指定種類として使う。
規約：KST A.5。使われ方：全境界の垂直部分。 -/
def IsVerticalShuffleFace {p n : ℕ} (s : ShuffleIndex p (n + 1)) (k : Fin (n + 2)) : Prop :=
  IsUniformShuffleFace (fun a ↦ a ∉ s.val) k

/-- 概要：垂直境界の条件は有限な所属判定で決定できる。
方針：定義の三つの場合を開く。
規約：KST A.5。使われ方：垂直境界の有限添字型。 -/
instance verticalShuffleFace_decidable {p n : ℕ} (s : ShuffleIndex p (n + 1))
    (k : Fin (n + 2)) : Decidable (IsVerticalShuffleFace s k) := by
  unfold IsVerticalShuffleFace IsUniformShuffleFace
  infer_instance

/-- 概要：水平境界と垂直境界は互いに素。
方針：最初・最後・内部の三つの場合で所属と非所属を比較する。
規約：KST A.5。使われ方：全境界添字の非交和への分類。 -/
lemma horizontal_vertical_shuffleFace_disjoint {p n : ℕ} (s : ShuffleIndex p (n + 1))
    (k : Fin (n + 2)) (hh : IsHorizontalShuffleFace s k) : ¬ IsVerticalShuffleFace s k := by
  rcases hh with ⟨rfl, hm⟩ | ⟨rfl, hm⟩ | ⟨a, rfl, hp, hq⟩
  · change ¬ IsUniformShuffleFace (fun a ↦ a ∉ s.val) 0
    rw [uniformShuffleFace_zero]
    exact not_not.mpr hm
  · change ¬ IsUniformShuffleFace (fun a ↦ a ∉ s.val) (Fin.last (n + 1))
    rw [uniformShuffleFace_last]
    exact not_not.mpr hm
  · change ¬ IsUniformShuffleFace (fun a ↦ a ∉ s.val) a.castSucc.succ
    rw [uniformShuffleFace_internal]
    tauto

/-- 概要：純粋境界でない頂点は最初でも最後でもない。
方針：各端点では水平所属か非所属の一方が必ず成立する。
規約：KST A.5。使われ方：混合境界の隣接ステップを復元する。 -/
lemma shuffleFace_not_pure_endpoints {p n : ℕ} (s : ShuffleIndex p (n + 1))
    (k : Fin (n + 2)) (hh : ¬ IsHorizontalShuffleFace s k) (hv : ¬ IsVerticalShuffleFace s k) :
    k ≠ 0 ∧ k ≠ Fin.last (n + 1) := by
  constructor
  · intro hk
    subst k
    have hH : ¬ (0 : Fin (n + 1)) ∈ s.val := fun hm ↦ hh (Or.inl ⟨rfl, hm⟩)
    exact hv (Or.inl ⟨rfl, hH⟩)
  · intro hk
    subst k
    have hH : Fin.last n ∉ s.val := fun hm ↦ hh (Or.inr (Or.inl ⟨rfl, hm⟩))
    exact hv (Or.inr (Or.inl ⟨rfl, hH⟩))

/-- 概要：最初・最後でない頂点は一意の隣接ステップの間にある。
方針：頂点番号から一つ引き、標準の内部番号を使う。
規約：KST A.5。使われ方：混合境界の添字の座標。 -/
lemma shuffleInternalVertex_eq {n : ℕ} (k : Fin (n + 2))
    (h₀ : k ≠ 0) (h₁ : k ≠ Fin.last (n + 1)) :
    (horizontalFaceInteriorRank k h₀ h₁).castSucc.succ = k := by
  apply Fin.ext
  change (k : ℕ) - 1 + 1 = (k : ℕ)
  have hn₀ : (k : ℕ) ≠ 0 := fun h ↦ h₀ (Fin.ext h)
  omega

/-- 概要：二つの純粋な種類以外の内部境界では、両隣のステップの種類は逆。
方針：両方水平・両方垂直の二つの場合を除く。
規約：KST A.5。使われ方：全境界の混合部分の条件。 -/
lemma shuffleFace_not_pure_mixed {p n : ℕ} (s : ShuffleIndex p (n + 1))
    (k : Fin (n + 2)) (hh : ¬ IsHorizontalShuffleFace s k) (hv : ¬ IsVerticalShuffleFace s k) :
    let he := shuffleFace_not_pure_endpoints s k hh hv
    let a := horizontalFaceInteriorRank k he.1 he.2
    a.castSucc ∈ s.val ↔ a.succ ∉ s.val := by
  let he := shuffleFace_not_pure_endpoints s k hh hv
  let a := horizontalFaceInteriorRank k he.1 he.2
  have hk : a.castSucc.succ = k := shuffleInternalVertex_eq k he.1 he.2
  have hH : ¬ (a.castSucc ∈ s.val ∧ a.succ ∈ s.val) := by
    intro hm
    apply hh
    rw [← hk]
    exact Or.inr (Or.inr ⟨a, rfl, hm.1, hm.2⟩)
  have hV : ¬ (a.castSucc ∉ s.val ∧ a.succ ∉ s.val) := by
    intro hm
    apply hv
    rw [← hk]
    exact Or.inr (Or.inr ⟨a, rfl, hm.1, hm.2⟩)
  tauto

/-- 概要：次数の端を含む純粋水平境界の型。
方針：水平ステップ数を減らさずに条件で制限する。
規約：KST A.5。使われ方：水平次数が零の場合も含む全境界の分類。 -/
abbrev AllHorizontalShuffleBoundaryIndex (p n : ℕ) :=
  {z : ShuffleIndex p (n + 1) × Fin (n + 2) // IsHorizontalShuffleFace z.1 z.2}

/-- 概要：次数の端を含む純粋垂直境界の型。
方針：垂直属性で全境界を制限する。
規約：KST A.5。使われ方：全境界の垂直部分。 -/
abbrev AllVerticalShuffleBoundaryIndex (p n : ℕ) :=
  {z : ShuffleIndex p (n + 1) × Fin (n + 2) // IsVerticalShuffleFace z.1 z.2}

/-- 概要：零個の内部頂点も許す混合境界の型。
方針：隣接するステップの種類が逆である対を取る。
規約：KST A.5。使われ方：全境界の混合部分。 -/
abbrev AllMixedShuffleBoundaryIndex (p n : ℕ) :=
  {z : ShuffleIndex p (n + 1) × Fin n // z.2.castSucc ∈ z.1.val ↔ z.2.succ ∉ z.1.val}

/-- 概要：混合境界は純粋水平でも純粋垂直でもない。
方針：内部頂点の二つの所属条件を比較する。
規約：KST A.5。使われ方：分類の逆写像の検証。 -/
lemma mixedShuffleFace_not_pure {p n : ℕ} (z : AllMixedShuffleBoundaryIndex p n) :
    ¬ IsHorizontalShuffleFace z.val.1 z.val.2.castSucc.succ ∧
      ¬ IsVerticalShuffleFace z.val.1 z.val.2.castSucc.succ := by
  have h := z.property
  change ¬ IsUniformShuffleFace (fun a ↦ a ∈ z.val.1.val) z.val.2.castSucc.succ ∧
    ¬ IsUniformShuffleFace (fun a ↦ a ∉ z.val.1.val) z.val.2.castSucc.succ
  rw [uniformShuffleFace_internal, uniformShuffleFace_internal]
  tauto

/-- 概要：全境界は水平・垂直・混合の三つの非交和に同値。
方針：純粋境界を先に判定し、それ以外では内部頂点からステップ番号を復元する。
規約：KST Construction A.5、零次の端も含む有限な実同値。
使われ方：三種類の境界和を全境界和へ合成する。 -/
def shuffleBoundaryPartitionEquiv (p n : ℕ) :
    AllHorizontalShuffleBoundaryIndex p n ⊕
      (AllVerticalShuffleBoundaryIndex p n ⊕ AllMixedShuffleBoundaryIndex p n) ≃
        ShuffleIndex p (n + 1) × Fin (n + 2) where
  toFun z := match z with
    | .inl z => z.val
    | .inr (.inl z) => z.val
    | .inr (.inr z) => (z.val.1, z.val.2.castSucc.succ)
  invFun z := if hh : IsHorizontalShuffleFace z.1 z.2 then .inl ⟨z, hh⟩
    else if hv : IsVerticalShuffleFace z.1 z.2 then .inr (.inl ⟨z, hv⟩)
    else .inr (.inr ⟨(z.1, horizontalFaceInteriorRank z.2
      (shuffleFace_not_pure_endpoints z.1 z.2 hh hv).1
      (shuffleFace_not_pure_endpoints z.1 z.2 hh hv).2),
        shuffleFace_not_pure_mixed z.1 z.2 hh hv⟩)
  left_inv z := by
    rcases z with z | (z | z)
    · simp only [dite_eq_left z.property]
    · have hh := horizontal_vertical_shuffleFace_disjoint z.val.1 z.val.2
      have hn : ¬ IsHorizontalShuffleFace z.val.1 z.val.2 := fun h ↦ hh h z.property
      simp only [dite_eq_right hn, dite_eq_left z.property]
    · have hn := mixedShuffleFace_not_pure z
      simp only [dite_eq_right hn.1, dite_eq_right hn.2]
      congr 2
  right_inv z := by
    by_cases hh : IsHorizontalShuffleFace z.1 z.2
    · simp only [dite_eq_left hh]
    · by_cases hv : IsVerticalShuffleFace z.1 z.2
      · simp only [dite_eq_right hh, dite_eq_left hv]
      · simp only [dite_eq_right hh, dite_eq_right hv]
        exact Prod.ext rfl (shuffleInternalVertex_eq z.2
          (shuffleFace_not_pure_endpoints z.1 z.2 hh hv).1
          (shuffleFace_not_pure_endpoints z.1 z.2 hh hv).2)

/-- 概要：全境界の有限和は三種類の境界和の和に一致。
方針：境界分類の実同値に沿って和を移す。
規約：KST A.5、任意の可換加法モノイドで成立。
使われ方：混合和の消滅と純粋境界和の組立。 -/
lemma shuffleBoundaryPartition_sum {A : Type*} [AddCommMonoid A] (p n : ℕ)
    (F : ShuffleIndex p (n + 1) × Fin (n + 2) → A) :
    (∑ s : ShuffleIndex p (n + 1), ∑ k : Fin (n + 2), F (s, k)) =
      (∑ z : AllHorizontalShuffleBoundaryIndex p n, F z.val) +
        ((∑ z : AllVerticalShuffleBoundaryIndex p n, F z.val) +
          ∑ z : AllMixedShuffleBoundaryIndex p n, F (z.val.1, z.val.2.castSucc.succ)) := by
  classical
  have ht := Fintype.sum_equiv (shuffleBoundaryPartitionEquiv p n)
    (fun z ↦ F (shuffleBoundaryPartitionEquiv p n z)) F (fun _ ↦ rfl)
  simpa only [Fintype.sum_prod_type, Fintype.sum_sum_type, shuffleBoundaryPartitionEquiv, Equiv.coe_fn_mk] using ht.symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

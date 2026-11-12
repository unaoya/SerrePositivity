module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExComplexity
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionCommutation
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionFaceCut

/-!
# Ex の単体ごとの拡張と対応先の一意性

概要：最小の複雑度を使って次元を上げる写像を構成し、その単射性を証明する。
方針：拡張退化の指定面で復元し、複雑度の上界を双方の表示で比較する。
規約：Moss 2020 Lemma 27。対応先の非退化性や型 II の条件は別の証明項目。
使われ方：X→Ex(X) の regular pairing の一意性の部分。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite
open scoped _root_.Simplicial

/--
概要：複雑度の閾値 k で拡張退化に前合成し、Ex の単体の次元を一つ上げる。
方針：細分上の r_n^k からの前合成を使う。
規約：Moss 2020 Theorem 22 の pairing に用いる写像。
使われ方：最小閾値での対応先の構成。
-/
def exExpansion (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1)) :
    (SSet.ex.obj X) _⦋n⦌ → (SSet.ex.obj X) _⦋n + 1⦌ :=
  fun s => ULift.up (subdivisionDegeneracyAt n k ≫ s.down)

/--
概要：拡張した単体の指定した面は元の単体である。
方針：Moss Lemma 26 (1) を前合成に適用する。
規約：欠けた面の添字は k+1。
使われ方：pairing の対応先から元の単体を復元する。
-/
theorem exExpansion_face (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (s : (SSet.ex.obj X) _⦋n⦌) :
    (SSet.ex.obj X).δ k.succ (exExpansion X n k s) = s := by
  apply ULift.ext
  change SimplexCategory.sd.map (SimplexCategory.δ k.succ) ≫
    (subdivisionDegeneracyAt n k ≫ s.down) = s.down
  rw [← Category.assoc, subdivisionDegeneracyAt_face, Category.id_comp]

/--
概要：複雑度 k 以下の単体を k で拡張すると、その像も複雑度 k 以下である。
方針：Moss Lemma 26 (4) の交換則を使う。
規約：高い次元での閾値は k.castSucc とする。
使われ方：異なる表示の複雑度を比較する。
-/
theorem exExpansion_complexity (X : SSet.{u}) (n : ℕ) (k : Fin (n + 1))
    (s : (SSet.ex.obj X) _⦋n⦌) (hs : s ∈ exComplexity X ⦋n⦌ k) :
    exExpansion X n k s ∈ exComplexity X ⦋n + 1⦌ k.castSucc := by
  change subdivisionCutAt ⦋n + 1⦌ k.castSucc ≫
    (subdivisionDegeneracyAt n k ≫ s.down) = subdivisionDegeneracyAt n k ≫ s.down
  rw [← Category.assoc, subdivisionDegeneracyAt_cut n k k le_rfl, Category.assoc]
  exact congrArg (fun f => subdivisionDegeneracyAt n k ≫ f) hs

/--
概要：閾値 h 以下の単体の任意の面も閾値 h 以下である。
方針：Moss Lemma 26 (5) の吸収則に固定点の等式を代入する。
規約：高い次元の閾値 h.castSucc は最後の閾値を除く。
使われ方：pairing の対応先の二つの表示の最小閾値を比べる。
-/
theorem exComplexity_face (X : SSet.{u}) (n : ℕ) (h : Fin (n + 1)) (i : Fin (n + 2))
    (s : (SSet.ex.obj X) _⦋n + 1⦌) (hs : s ∈ exComplexity X ⦋n + 1⦌ h.castSucc) :
    (SSet.ex.obj X).δ i s ∈ exComplexity X ⦋n⦌ h := by
  change subdivisionCutAt ⦋n⦌ h ≫ (SimplexCategory.sd.map (SimplexCategory.δ i) ≫ s.down) =
    SimplexCategory.sd.map (SimplexCategory.δ i) ≫ s.down
  change subdivisionCutAt ⦋n + 1⦌ h.castSucc ≫ s.down = s.down at hs
  calc
    _ = subdivisionCutAt ⦋n⦌ h ≫ (SimplexCategory.sd.map (SimplexCategory.δ i) ≫
        (subdivisionCutAt ⦋n + 1⦌ h.castSucc ≫ s.down)) := by rw [hs]
    _ = (subdivisionCutAt ⦋n⦌ h ≫ SimplexCategory.sd.map (SimplexCategory.δ i) ≫
        subdivisionCutAt ⦋n + 1⦌ h.castSucc) ≫ s.down := by simp only [Category.assoc]
    _ = (SimplexCategory.sd.map (SimplexCategory.δ i) ≫
        subdivisionCutAt ⦋n + 1⦌ h.castSucc) ≫ s.down :=
      congrArg (fun f => f ≫ s.down) (subdivisionCutAt_face_absorb n i h)
    _ = _ := by rw [Category.assoc, hs]

/--
概要：単体の最小の複雑度を使った、次元を一つ上げる標準写像。
方針：固定点フィルターの最小閾値で拡張退化に前合成する。
規約：Moss 2020 Theorem 22 の pairing の単体ごとの候補。
使われ方：対応先の一意性と非退化性の検証。
-/
def exPairingStep (X : SSet.{u}) (n : ℕ) :
    (SSet.ex.obj X) _⦋n⦌ → (SSet.ex.obj X) _⦋n + 1⦌ :=
  fun s => exExpansion X n (exComplexityLevel X ⦋n⦌ s) s

/--
概要：最小の複雑度で次元を上げる写像は単射である。
方針：二つの表示で複雑度の上界を比べて閾値を一致させ、指定面で元へ戻る。
規約：Moss 2020 Lemma 27。ここでは全単体を扱い、非退化性はまだ主張しない。
使われ方：regular pairing の対応先の一意性。
-/
theorem exPairingStep_injective (X : SSet.{u}) (n : ℕ) :
    Function.Injective (exPairingStep X n) := by
  intro s t h
  let k := exComplexityLevel X ⦋n⦌ s
  let l := exComplexityLevel X ⦋n⦌ t
  have he : exExpansion X n k s = exExpansion X n l t := h
  have hsk : exExpansion X n k s ∈ exComplexity X ⦋n + 1⦌ k.castSucc :=
    exExpansion_complexity X n k s (exComplexityLevel_mem X ⦋n⦌ s)
  have htl : exExpansion X n l t ∈ exComplexity X ⦋n + 1⦌ l.castSucc :=
    exExpansion_complexity X n l t (exComplexityLevel_mem X ⦋n⦌ t)
  have hkl : k ≤ l := by
    have hs := exComplexity_face X n l k.succ (exExpansion X n k s) (he.symm ▸ htl)
    rw [exExpansion_face] at hs
    exact (exComplexityLevel_le_iff X ⦋n⦌ s l).mpr hs
  have hlk : l ≤ k := by
    have ht := exComplexity_face X n k l.succ (exExpansion X n l t) (he ▸ hsk)
    rw [exExpansion_face] at ht
    exact (exComplexityLevel_le_iff X ⦋n⦌ t k).mpr ht
  have hlevels : k = l := le_antisymm hkl hlk
  have he' : exExpansion X n k s = exExpansion X n k t := by
    simpa only [hlevels] using he
  have hfaces := congrArg (fun r => (SSet.ex.obj X).δ k.succ r) he'
  simpa only [exExpansion_face] using hfaces

/--
概要：最小閾値で拡張した単体の複雑度の上界は元の単体と同じである。
方針：順方向は閾値の単調性、逆方向は指定した面の複雑度を使う。
規約：Moss 2020 Lemma 27 の最小閾値の比較の補助。
使われ方：拡張前後の複雑度の一致。
-/
theorem exPairingStep_complexity_iff (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌) (h : Fin (n + 1)) :
    s ∈ exComplexity X ⦋n⦌ h ↔ exPairingStep X n s ∈ exComplexity X ⦋n + 1⦌ h.castSucc := by
  let k := exComplexityLevel X ⦋n⦌ s
  constructor
  · intro hs
    have hk : k ≤ h := (exComplexityLevel_le_iff X ⦋n⦌ s h).mpr hs
    exact exComplexity_mono X ⦋n + 1⦌ (Fin.castSucc_le_castSucc_iff.mpr hk)
      (exExpansion_complexity X n k s (exComplexityLevel_mem X ⦋n⦌ s))
  · intro hs
    have hf := exComplexity_face X n h k.succ (exPairingStep X n s) hs
    change (SSet.ex.obj X).δ k.succ (exExpansion X n k s) ∈ exComplexity X ⦋n⦌ h at hf
    rw [exExpansion_face] at hf
    exact hf

/--
概要：最小閾値で拡張した単体は同じ最小の複雑度を持つ。
方針：閾値の上界の同値を、最小閾値と最後の閾値の手前への制限に適用する。
規約：Moss 2020 Lemmas 27–29 の複雑度の比較。
使われ方：pairing の型と先行関係の制御。
-/
theorem exPairingStep_complexityLevel (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌) :
    exComplexityLevel X ⦋n + 1⦌ (exPairingStep X n s) = (exComplexityLevel X ⦋n⦌ s).castSucc := by
  let k := exComplexityLevel X ⦋n⦌ s
  let l := exComplexityLevel X ⦋n + 1⦌ (exPairingStep X n s)
  have hle : l ≤ k.castSucc := (exComplexityLevel_le_iff X ⦋n + 1⦌ _ k.castSucc).mpr
    ((exPairingStep_complexity_iff X n s k).mp (exComplexityLevel_mem X ⦋n⦌ s))
  have hne : l ≠ Fin.last (n + 1) := (hle.trans_lt k.castSucc_lt_last).ne
  let h := l.castPred hne
  have hcast : h.castSucc = l := Fin.castSucc_castPred l hne
  have ht : exPairingStep X n s ∈ exComplexity X ⦋n + 1⦌ h.castSucc := by
    rw [hcast]
    exact exComplexityLevel_mem X ⦋n + 1⦌ _
  have hkh : k ≤ h := (exComplexityLevel_le_iff X ⦋n⦌ s h).mpr
    ((exPairingStep_complexity_iff X n s h).mpr ht)
  exact le_antisymm hle ((Fin.castSucc_le_castSucc_iff.mpr hkh).trans_eq hcast)

/--
概要：最小閾値で拡張した単体が元の X の像に入ることは、元の単体が像に入ることに等しい。
方針：複雑度零の固定点と単位の像の一致を使う。
規約：Moss 2020 Lemma 29 の対応先が元の部分対象に入らないことの部分。
使われ方：regular pairing が追加単体の集合の内部で定義されること。
-/
theorem exPairingStep_mem_image_iff (X : SSet.{u}) (n : ℕ)
    (s : (SSet.ex.obj X) _⦋n⦌) :
    exPairingStep X n s ∈ Set.range ((exUnitAt X).app (op ⦋n + 1⦌)) ↔
      s ∈ Set.range ((exUnitAt X).app (op ⦋n⦌)) := by
  rw [← exComplexity_zero, ← exComplexity_zero]
  exact (exPairingStep_complexity_iff X n s 0).symm

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor

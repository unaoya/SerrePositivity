module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialSpineSimplexPairing
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Inner.Basic

/-!
概要：可算 spine の包含は正則な内部頂点挿入の pairing により inner anodyne。
方針：欠ける頂点の前後に元の頂点があることを、元の面番号の両端不在へ移す。
規約：可算 nerve の元の単体を扱い、モデル構造の instance を要求しない。
使われ方：P-11 の望遠鏡から可算 nerve への全余錐比較。

対応節は Kerodon 1.5（Tag 0055）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories

/-- 概要：可算 nerve の余次元一の面で、内部頂点を欠くなら面番号も内部。
方針：厳密単調な頂点列の単射性で欠ける頂点を同定し、前後の頂点と比較する。
規約：全頂点列の像と元の面の等式を入力する。
使われ方：有限頂点集合の pairing から inner horn の接合へ移す。 -/
lemma sequentialNerveFace_innerIndex {d : ℕ}
    (x : (nerve (ULift.{u} ℕ)) _⦋d⦌) (y : (nerve (ULift.{u} ℕ)) _⦋d + 1⦌)
    (hy : y ∈ (nerve (ULift.{u} ℕ)).nonDegenerate (d + 1)) (k : Fin (d + 2))
    (hk : (nerve (ULift.{u} ℕ)).δ k y = x) (p : ℕ)
    (hs : Finset.univ.image (fun i ↦ (y.obj i).down) =
      insert p (Finset.univ.image (fun i ↦ (x.obj i).down)))
    (hin : ∃ a ∈ Finset.univ.image (fun i ↦ (x.obj i).down),
      ∃ b ∈ Finset.univ.image (fun i ↦ (x.obj i).down), a < p ∧ p < b) :
    k ≠ 0 ∧ k ≠ Fin.last (d + 1) := by
  have hyinj := (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono y).mp hy |>.injective
  have he (i : Fin (d + 1)) : (y.obj (k.succAbove i)).down = (x.obj i).down := by
    exact congrArg (fun f ↦ (f.obj i).down) hk
  have hmiss : (y.obj k).down ∉ Finset.univ.image (fun i ↦ (x.obj i).down) := by
    intro hv
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hv
    exact Fin.succAbove_ne _ _ (hyinj (ULift.ext ((he i).trans hi)))
  have hpoint : (y.obj k).down = p := by
    have hm : (y.obj k).down ∈ Finset.univ.image (fun i ↦ (y.obj i).down) :=
      Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩
    rw [hs] at hm
    exact (Finset.mem_insert.mp hm).resolve_right hmiss
  obtain ⟨a, ha, b, hb, hap, hpb⟩ := hin
  obtain ⟨ia, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨ib, _, rfl⟩ := Finset.mem_image.mp hb
  constructor
  · intro hz
    have hm := y.monotone (show k ≤ k.succAbove ia by rw [hz]; exact Fin.zero_le _)
    change (y.obj k).down ≤ (y.obj (k.succAbove ia)).down at hm
    rw [hpoint, he ia] at hm
    exact (not_le_of_gt hap) hm
  · intro hn
    have hm := y.monotone (show k.succAbove ib ≤ k by rw [hn]; exact Fin.le_last _)
    change (y.obj (k.succAbove ib)).down ≤ (y.obj k).down at hm
    rw [hpoint, he ib] at hm
    exact (not_le_of_gt hpb) hm

/-- 概要：内部頂点を挿入した非退化単体の一意な面番号は両端ではない。
方針：元の次元付き単体を取り出し、頂点列の内部点判定を使う。
規約：元の一意な余次元一の面を比較する。
使われ方：pairing の inner 条件を次元付きの型へ移す。 -/
lemma sequentialNerveUniqueFace_innerIndex
    (x y : (nerve (ULift.{u} ℕ)).N) (h : x.toS.IsUniquelyCodimOneFace y.toS) (p : ℕ)
    (hs : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport y = insert p (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport x))
    (hin : ∃ a ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport x, ∃ b ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport x, a < p ∧ p < b) :
    h.index rfl ≠ 0 ∧ h.index rfl ≠ Fin.last (x.dim + 1) := by
  obtain ⟨d, a, rfl⟩ := x.mk_surjective
  obtain ⟨e, b, rfl⟩ := y.mk_surjective
  obtain rfl : e = d + 1 := h.dim_eq
  exact sequentialNerveFace_innerIndex a.val b.val b.property (h.index rfl)
    (h.δ_index rfl) p hs hin

/-- 概要：可算 spine の pairing の欠ける面番号は両端ではない。
方針：頂点集合の挿入の式と挿入点の内部性を、元の余次元一の面へ渡す。
規約：pairing が選んだ実際の面番号を比較する。
使われ方：可算 spine の pairing の inner 条件。 -/
lemma sequentialSpinePairing_innerIndex (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePairing.{u}.II) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePairing.isUniquelyCodimOneFace s).index rfl ≠ 0 ∧
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePairing.isUniquelyCodimOneFace s).index rfl ≠
        Fin.last (s.val.dim + 1) := by
  exact sequentialNerveUniqueFace_innerIndex s.val.toN (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePairing.p s).val.toN
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePairing.isUniquelyCodimOneFace s) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePairing_support s)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePivot_interior (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpineOutsideSimplexEquiv s.val).property)

/-- 概要：可算 spine の正則 pairing は内部ホーンだけを接合する。
方針：実際の面番号の両端不在を全ての対に適用する。
規約：有限な部分列への制限は不要。
使われ方：可算 spine 包含の inner anodyne 性。 -/
instance sequentialSpinePairing_isInner : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePairing.{u}.IsInner where
  ne_zero s d hd := by
    subst d
    exact (sequentialSpinePairing_innerIndex s).1
  ne_last s d hd := by
    subst d
    exact (sequentialSpinePairing_innerIndex s).2

/-- 概要：可算 spine から元の可算 nerve への包含は inner anodyne。
方針：構成した正則な内部頂点挿入の pairing を既存の接合定理へ渡す。
規約：元の包含そのものについて主張する。
使われ方：可算列の余極限を隣接辺の望遠鏡で計算する。 -/
lemma sequentialSpine_inclusion_innerAnodyne : innerAnodyneExtensions _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.{u}.ι :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpinePairing.innerAnodyneExtensions

/-- 概要：可算 spine への全関手の制限は、任意の quasicategory 値で同値。
方針：包含の inner anodyne 性を既存の前合成同値の判定へ渡す。
規約：spine 自体の quasicategory 性は要求しない。
使われ方：元の可算図式の全余錐の保存と反映。 -/
lemma sequentialSpine_inclusion_isPrecompositionEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialSpine.{u}.ι :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_of_innerAnodyne _ sequentialSpine_inclusion_innerAnodyne

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories

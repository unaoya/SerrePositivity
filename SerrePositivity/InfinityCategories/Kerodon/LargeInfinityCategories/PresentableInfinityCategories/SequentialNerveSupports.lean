module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.Data.Finset.Sort

/-!
概要：可算順序圏の非退化単体を、非空な自然数の有限集合で表示する。
方針：厳密単調な頂点列の像を取り、逆方向には有限集合を昇順に列挙する。
規約：元の持ち上げた自然数の nerve を保ち、次元を含む全非退化単体を扱う。
使われ方：P-11 の可算 spine の inner horn pairing とその整礎順位。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：可算 nerve の非退化単体の全頂点番号を集める。
方針：元の有限な頂点列の像を有限集合として取る。
規約：持ち上げ前の自然数の番号を記録する。
使われ方：spine の領域外の単体の組合せ論的表示。 -/
def sequentialNerveSupport (s : (nerve (ULift.{u} ℕ)).N) : Finset ℕ :=
  Finset.univ.image (fun i ↦ (s.simplex.obj i).down)

/-- 概要：非退化な可算 nerve 単体の頂点番号は厳密単調。
方針：poset の nerve の非退化性の判定を元の頂点列へ適用する。
規約：退化単体の頂点列には主張しない。
使われ方：頂点集合の濃度と一意性。 -/
lemma sequentialNerveSupport_strictMono (s : (nerve (ULift.{u} ℕ)).N) :
    StrictMono (fun i ↦ (s.simplex.obj i).down) :=
  (PartialOrder.mem_nerve_nonDegenerate_iff_strictMono s.simplex).mp s.nonDegenerate

/-- 概要：頂点集合の濃度は非退化単体の次元に一を加えたもの。
方針：厳密単調性による単射な像の濃度を計算する。
規約：零次元も含む。
使われ方：頂点の一つの挿入と余次元一の対応。 -/
lemma sequentialNerveSupport_card (s : (nerve (ULift.{u} ℕ)).N) :
    (sequentialNerveSupport s).card = s.dim + 1 := by
  rw [sequentialNerveSupport, Finset.card_image_of_injective _
    (sequentialNerveSupport_strictMono s).injective]
  exact Finset.card_fin _

/-- 概要：非退化単体の頂点集合は非空。
方針：その濃度が正であることを使う。
規約：全ての次元を扱う。
使われ方：有限集合の昇順列挙の始点。 -/
lemma sequentialNerveSupport_nonempty (s : (nerve (ULift.{u} ℕ)).N) :
    (sequentialNerveSupport s).Nonempty := by
  rw [← Finset.card_pos, sequentialNerveSupport_card]
  omega

/-- 概要：元の可算 nerve の非退化単体はその頂点集合で一意に決まる。
方針：濃度で次元を揃え、厳密単調な二つの列は同じ像なら等しいことを使う。
規約：次元を含む型 N の単射性を返す。
使われ方：spine の pairing の一意性と面関係の判定。 -/
lemma sequentialNerveSupport_injective : Function.Injective sequentialNerveSupport.{u} := by
  intro s t h
  obtain ⟨n, x, rfl⟩ := s.mk_surjective
  obtain ⟨m, y, rfl⟩ := t.mk_surjective
  have hc := congrArg Finset.card h
  rw [sequentialNerveSupport_card, sequentialNerveSupport_card] at hc
  change n + 1 = m + 1 at hc
  obtain rfl : n = m := Nat.add_right_cancel hc
  have hx := sequentialNerveSupport_strictMono (SSet.N.mk x.val x.property)
  have hy := sequentialNerveSupport_strictMono (SSet.N.mk y.val y.property)
  change Finset.univ.image (fun i ↦ (x.val.obj i).down) =
    Finset.univ.image (fun i ↦ (y.val.obj i).down) at h
  have hr : Set.range (fun i ↦ (x.val.obj i).down) =
      Set.range (fun i ↦ (y.val.obj i).down) := by
    ext k
    constructor
    · rintro ⟨i, hi⟩
      have hm : (x.val.obj i).down ∈ Finset.univ.image (fun j ↦ (x.val.obj j).down) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      rw [h] at hm
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
      exact ⟨j, hj.trans hi⟩
    · rintro ⟨i, hi⟩
      have hm : (y.val.obj i).down ∈ Finset.univ.image (fun j ↦ (y.val.obj j).down) :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
      rw [← h] at hm
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
      exact ⟨j, hj.trans hi⟩
  have hv := (hx.range_inj_of_wellFoundedLT hy).mp hr
  have hxy : x.val = y.val := by
    exact CategoryTheory.Functor.ext
      (fun i ↦ ULift.ext (congrFun hv i)) (fun _ _ _ ↦ Subsingleton.elim _ _)
  obtain rfl : x = y := Subtype.ext hxy
  rfl

/-- 概要：自然数の非空な有限集合を、元の可算 nerve の非退化単体へ昇順列挙する。
方針：頂点数から次元を定め、有限集合の順序埋め込みを持ち上げる。
規約：列挙の像は元の有限集合そのもの。
使われ方：頂点挿入の操作を単体の操作へ戻す。 -/
def sequentialNerveSimplexOfSupport (S : Finset ℕ) (hS : S.Nonempty) :
    (nerve (ULift.{u} ℕ)).N := by
  let n := S.card - 1
  have hc : S.card = n + 1 := (Nat.sub_add_cancel (Finset.card_pos.mpr hS)).symm
  let a := S.orderEmbOfFin hc
  let x : (nerve (ULift.{u} ℕ)) _⦋n⦌ :=
    (show Monotone (fun i : Fin (n + 1) ↦ (ULift.up (a i) : ULift.{u} ℕ)) from
      a.monotone).functor
  refine SSet.N.mk x ((PartialOrder.mem_nerve_nonDegenerate_iff_strictMono x).mpr ?_)
  exact a.strictMono

/-- 概要：有限集合の昇順列挙から、元の同じ頂点集合を回収する。
方針：順序埋め込みによる全有限集合の像を計算する。
規約：集合の同型でなく有限集合の等式。
使われ方：頂点集合と非退化単体の全単射。 -/
lemma sequentialNerveSimplexOfSupport_support (S : Finset ℕ) (hS : S.Nonempty) :
    sequentialNerveSupport (sequentialNerveSimplexOfSupport.{u} S hS) = S := by
  exact Finset.image_orderEmbOfFin_univ S _

/-- 概要：可算 nerve の全非退化単体と、非空な自然数の有限集合の全単射。
方針：頂点集合の単射性と昇順列挙の全射性を結合する。
規約：元の宇宙 u の nerve の単体を返す。
使われ方：spine の組合せ論的 pairing を全単体集合へ移す。 -/
def sequentialNerveSupportEquiv :
    (nerve (ULift.{u} ℕ)).N ≃ {S : Finset ℕ // S.Nonempty} :=
  Equiv.ofBijective
    (fun s : (nerve (ULift.{u} ℕ)).N ↦
      ⟨sequentialNerveSupport s, sequentialNerveSupport_nonempty s⟩) (by
      constructor
      · intro s t h
        exact sequentialNerveSupport_injective (congrArg Subtype.val h)
      · intro S
        exact ⟨sequentialNerveSimplexOfSupport.{u} S.val S.property,
          Subtype.ext (sequentialNerveSimplexOfSupport_support.{u} S.val S.property)⟩)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

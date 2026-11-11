module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.SimplicialReplacementConstant

/-!
概要：有限順序の末尾への包含と、零から始まらない射列の因子化。
方針：各頂点に後者を足す包含を使い、零を避ける射列の全頂点から一を引く。
規約：底の有限順序を ULift で係数と同じ宇宙に置く。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、Theorem 5.3.5.7（Tag 037Q）、末尾部分との pushout 分解。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：有限順序の末尾部分を全体へ含める関手。
方針：各頂点 i を i+1 に写す単調写像を使う。
規約：始域は n+1 頂点、標的は n+2 頂点を持つ。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、零頂点を除いた部分の包含。 -/
def scaffoldFiniteTail (n : ℕ) :
    ULift.{u} (Fin (n + 1)) ⥤ ULift.{u} (Fin (n + 2)) :=
  (show ULift.{u} (Fin (n + 1)) →o ULift.{u} (Fin (n + 2)) from
    { toFun := fun i ↦ ULift.up i.down.succ
      monotone' := fun _ _ h ↦ Nat.succ_le_succ h }).monotone.functor

/-- 概要：有限順序の零頂点は始対象。
方針：零以下から任意の頂点への順序射と射の一意性を使う。
規約：宇宙を上げた有限順序にも同じ構成を使う。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、最初の係数値からの組み立て射。 -/
def scaffoldFiniteInitial (n : ℕ) : IsInitial (ULift.up (0 : Fin (n + 1)) : ULift.{u} _) :=
  IsInitial.ofUniqueHom (fun i ↦ homOfLE (Fin.zero_le i.down))
    (fun _ _ ↦ Subsingleton.elim _ _)

/-- 概要：有限順序の射列の各頂点から一を引いて末尾の添字に戻す。
方針：自然数の切り捨てた引き算の単調性を使って射列を作る。
規約：零を避ける射列に適用したとき、末尾への包含による因子化を与える。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、末尾部分に含まれる単体の表示。 -/
def scaffoldFiniteTailFactor {n m : ℕ}
    (σ : ComposableArrows (ULift.{u} (Fin (n + 2))) m) :
    ComposableArrows (ULift.{u} (Fin (n + 1))) m where
  obj i := ULift.up ⟨(σ.obj i).down.val - 1, by
    have h := (σ.obj i).down.isLt
    omega⟩
  map {i j} f := homOfLE (by
    have h : σ.obj i ≤ σ.obj j := leOfHom (σ.map f)
    change (σ.obj i).down.val ≤ (σ.obj j).down.val at h
    exact Nat.sub_le_sub_right h 1)

/-- 概要：有限順序の射列が零から始まらなければ全頂点が零を避ける。
方針：始点から各頂点への射の単調性と始点の正値性を使う。
規約：始点が零でないという条件だけを要求する。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、末尾への因子化の前提。 -/
lemma scaffoldFiniteChain_positive {n m : ℕ}
    (σ : ComposableArrows (ULift.{u} (Fin (n + 2))) m)
    (h : (σ.obj 0).down ≠ 0) (i : Fin (m + 1)) : 0 < (σ.obj i).down.val := by
  have hi := leOfHom (σ.map (homOfLE (Fin.zero_le i)))
  have h0 : (σ.obj 0).down.val ≠ 0 := fun he ↦ h (Fin.ext he)
  change (σ.obj 0).down.val ≤ (σ.obj i).down.val at hi
  omega

/-- 概要：零から始まらない射列は末尾の包含を経由する。
方針：各頂点で一を引いて戻す操作が逆になることと、順序圏の射の一意性を使う。
規約：関手の厳密な等式として因子化を与える。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、pushout 分解の単体ごとの被覆。 -/
lemma scaffoldFiniteTailFactor_comp {n m : ℕ}
    (σ : ComposableArrows (ULift.{u} (Fin (n + 2))) m)
    (h : (σ.obj 0).down ≠ 0) :
    scaffoldFiniteTailFactor σ ⋙ scaffoldFiniteTail n = σ := by
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  apply ULift.ext
  apply Fin.ext
  change (σ.obj i).down.val - 1 + 1 = (σ.obj i).down.val
  have hi := scaffoldFiniteChain_positive σ h i
  omega

/-- 概要：有限順序の末尾の nerve の包含は単射。
方針：各次数の射列は頂点ごとの後者写像の単射性で復元できる。
規約：順序圏の射の一意性で射列の射の部分の一致を示す。
使われ方：Kerodon Remark 5.3.2.12（Tag 0252）、pushout の末尾部分の単射性。 -/
instance scaffoldFiniteTail_nerveMap_mono (n : ℕ) : Mono (nerveMap (scaffoldFiniteTail.{u} n)) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [mono_iff_injective]
  intro σ τ h
  change σ ⋙ scaffoldFiniteTail n = τ ⋙ scaffoldFiniteTail n at h
  refine CategoryTheory.Functor.ext (fun i ↦ ?_) (fun _ _ _ ↦ Subsingleton.elim _ _)
  have hi := congrArg (fun ξ : ComposableArrows (ULift.{u} (Fin (n + 2))) d.unop.len ↦
    (ξ.obj i).down.val) h
  apply ULift.ext
  apply Fin.ext
  change (σ.obj i).down.val + 1 = (τ.obj i).down.val + 1 at hi
  omega

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

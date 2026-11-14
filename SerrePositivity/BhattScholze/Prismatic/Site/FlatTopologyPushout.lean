module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.Site.FlatCoverPushout
import all SerrePositivity.BhattScholze.Prismatic.Site.FlatCover
import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCover
import SerrePositivity.BhattScholze.Prism.Bounded.CompletedTensorCardinal
import SerrePositivity.BhattScholze.Prism.Bounded.CompletelyFlatPrism

/-!
# 平坦な被覆の底変換

## 概要
有界 prism の site で忠実平坦な被覆の押し出しは存在し、底変換した射も被覆。

## 方針
完備テンソル積の完全忠実平坦性から有界 prism を作り、有限剰余で濃度を評価する。

## 規約
BS 著者版 Corollary 3.12 (a) の固定基底の affine site。濃度上限は許容するものを選ぶ。

## 使われ方
単一射の被覆で生成する平坦位相。
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PrismOver

open CategoryTheory CategoryTheory.Limits DerivedCompletion
open scoped Cardinal

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : OrientedPrism p A}
variable {R : Type u} [CommRing R] [Algebra (A ⧸ P.ideal) R] {κ : Cardinal.{u}}

/-- 概要：忠実平坦な被覆を任意の射に沿って押し出せる。
方針：完備テンソル積の完全忠実平坦性・濃度・普遍性を合わせる。
規約：BS 著者版 Corollary 3.12 (a)。許容濃度を固定する。
使われ方：被覆の底変換公理。 -/
theorem exists_isPushout_isFaithfullyFlat (hκ : IsAdmissibleCutoff P R κ)
    {X Y X' : PrismOver P R κ} (f : X ⟶ Y) (hf : IsFaithfullyFlat f) (g : X ⟶ X') :
    ∃ (Y' : PrismOver P R κ) (f' : X' ⟶ Y') (g' : Y ⟶ Y'),
      IsPushout f g g' f' ∧ IsFaithfullyFlat f' := by
  let := f.toHom.toRingHom.toAlgebra
  let := g.toHom.toRingHom.toAlgebra
  let T := PrismCompletedTensor (A := X.B) (C := Y.B) X'.Q
  let l : X'.B →+* T := prismCompletedTensorLeft X'.Q
  let := l.toAlgebra
  have hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : X'.B), X'.Q.generator}) T :=
    prismCompletedTensor_completelyFaithfullyFlat X.Q X'.Q X'.bounded
      g.toHom f.toHom.toRingHom hf
  let D := prismCompletedTensorDelta X'.Q X.Q.deltaStructure Y.Q.deltaStructure
    g.toHom.map_delta f.toHom.map_delta
  have hl := prismCompletedTensorLeft_isDeltaHom X'.Q X.Q.deltaStructure Y.Q.deltaStructure
    g.toHom.map_delta f.toHom.map_delta
  obtain ⟨Q, _, _, hgen, _, hQ⟩ := exists_boundedPrism_of_completelyFlat_deltaAlgebra
    X'.Q X'.bounded D l hl (prismCompletedTensor_complete_p X'.Q)
    (prismCompletedTensor_complete_generator X'.Q) hflat.1
  have hc : IsAdicComplete (Ideal.span {(p : T), l X'.Q.generator}) T := by
    rw [← hgen]
    exact _root_.SerrePositivity.BhattScholze.boundedPrism_pair_isAdicComplete Q hQ
  have hκ₀ : ℵ₀ ≤ κ := by
    apply le_trans ?_ hκ.1
    unfold cutoff
    apply le_trans ?_ (Cardinal.self_le_power _ Cardinal.one_le_aleph0)
    rw [add_comm]
    exact le_self_add
  have hsmall := prismCompletedTensor_mk_le X'.Q hκ₀ hκ.2 X'.small Y.small hc
  exact exists_isPushout_of_completedTensor_completelyFaithfullyFlat f g hsmall hflat

end SerrePositivity.BhattScholze.Prismatic.PrismOver

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 3.12" (partial := special) "固定基底 (A,(d)) 上・濃度 cutoff の site（D22）。(a) 完全平坦な押し出し、構造環と d 剰余の全次数の Čech 完全性と層条件（BS-W15 K4）。∞ 層・RΓ への接続は drafts ／ 11-11 更新（2） ／ 11-12 夜更新（§3 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.PrismOver.exists_isPushout_isFaithfullyFlat

module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionBottomPointCut
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPlusParent
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionHorizontalFaithful
public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionPrefixBottomMerge

/-!
概要：最初の一点の実因子を生成射の定値関手へ照合し、残りの始点plusの実関手を回収する。
方針：一点への全実射の一意性と、構成済みの実区間分解の全合成を使う。
規約：前置すると元の実全関手へ戻る等式を構成する。
使われ方：Riehl–Verity Lemma 4.1.4の実親の逆方向、HA Proposition 4.7.3.3、
Kerodon Remark 6.2.1.4（Tag 02EN）の前の実始点plus因子の回収。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：一点の終点への元の実射は一意。
方針：実射の忠実な順序表示で全点の像が値0であることを使う。
規約：四Homの全実射。使われ方：Riehl–Verity Lemma 4.1.4の一点の前置因子。 -/
lemma walkingAdjunctionHom_ext_of_card_one_target {X Y : WalkingAdjunctionPoint}
    {A B : walkingAdjunctionHom X Y} (f g : A ⟶ B)
    (hc : walkingAdjunctionOrdinalCard X Y B = 1) : f = g := by
  apply walkingAdjunctionOrderHom_injective
  apply OrderHom.ext
  funext i
  apply Fin.ext
  have hf := (walkingAdjunctionOrderHom f i).isLt
  have hg := (walkingAdjunctionOrderHom g i).isLt
  omega

/-- 概要：切り出した最初の一点の実因子は実生成射の定値関手。
方針：全実対象の個数1と一点への実射の一意性を全関手の等式へ戻す。
規約：全自然性を保持する。使われ方：Riehl–Verity Lemma 4.1.4の前置生成射の検収。 -/
lemma walkingAdjunctionBottomPointFactorization_left {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) :
    (walkingAdjunctionBottomPointFactorization H hno hlast).left =
      (CategoryTheory.Functor.const (Fin (n + 1))).obj
        (walkingAdjunctionGeneratorVertex .minus) := by
  let d := walkingAdjunctionBottomPointFactorization H hno hlast
  have ho (i : Fin (n + 1)) : d.left.obj i = walkingAdjunctionGeneratorVertex .minus := by
    apply walkingAdjunctionOrdinalCard_injective .minus .plus
    exact walkingAdjunctionBottomPointFactorization_left_card H hno hlast i
  refine CategoryTheory.Functor.hext ho ?_
  intro i j f
  apply (conj_eqToHom_iff_heq _ _ (ho i) (ho j)).mp
  exact walkingAdjunctionHom_ext_of_card_one_target _ _
    (walkingAdjunctionBottomPointFactorization_left_card H hno hlast j)

/-- 概要：最初の一点を除いた残りを、始点plusの実全関手として回収する。
方針：構成した実水平分解の右因子を取る。
規約：全実射を含む実関手。使われ方：Riehl–Verity Lemma 4.1.4の実親の逆方向。 -/
def walkingAdjunctionRemoveBottomPrefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) :
    ComposableArrows (walkingAdjunctionHom .plus Y) n :=
  (walkingAdjunctionBottomPointFactorization H hno hlast).right

/-- 概要：回収した始点plusの実関手へ生成射を前置すると元の実全鎖。
方針：実左因子を生成射の定値関手へ同一視し、実区間分解の全合成を使う。
規約：全実関手の等式を結論にする。使われ方：Riehl–Verity Lemma 4.1.4の逆の照合。 -/
lemma walkingAdjunctionRemoveBottomPrefix_prefix {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) :
    walkingAdjunctionPlusParentPrefix (walkingAdjunctionRemoveBottomPrefix H hno hlast) = H := by
  let d := walkingAdjunctionBottomPointFactorization H hno hlast
  have hl : d.left = (CategoryTheory.Functor.const (Fin (n + 1))).obj
      (walkingAdjunctionGeneratorVertex .minus) :=
    walkingAdjunctionBottomPointFactorization_left H hno hlast
  change ((CategoryTheory.Functor.const (Fin (n + 1))).obj
    (walkingAdjunctionGeneratorVertex .minus)).prod' d.right ⋙
      walkingAdjunctionHorizontal .minus .plus Y = H
  rw [← hl]
  exact d.fac

/-- 概要：回収した実因子の点の個数に1を加えると元の個数。
方針：前置による全関手の回収を各実頂点で評価する。
規約：全頂点の実個数。使われ方：Riehl–Verity Lemma 4.1.4の実原子の端点の回収。 -/
lemma walkingAdjunctionRemoveBottomPrefix_card {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .minus Y) n)
    (hno : ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y (H.obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        (H.map (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0)
    (hlast : walkingAdjunctionOrdinalCard .minus Y (H.obj (Fin.last n)) = 2) (i : Fin (n + 1)) :
    1 + walkingAdjunctionOrdinalCard .plus Y
      ((walkingAdjunctionRemoveBottomPrefix H hno hlast).obj i) =
        walkingAdjunctionOrdinalCard .minus Y (H.obj i) := by
  have he := congrArg (walkingAdjunctionOrdinalCard .minus Y)
    (CategoryTheory.Functor.congr_obj (walkingAdjunctionRemoveBottomPrefix_prefix H hno hlast) i)
  exact (walkingAdjunctionPlusParentPrefix_card _ i).symm.trans he

/-- 概要：実生成射の前置は全実関手を区別する。
方針：個数から右因子の全対象を回収し、実水平合成の忠実性で全射を戻す。
規約：元の全関手の単射性。使われ方：Riehl–Verity Lemma 4.1.4の実因子の一意性。 -/
lemma walkingAdjunctionPlusParentPrefix_injective {n : ℕ} {Y : WalkingAdjunctionPoint} :
    Function.Injective (walkingAdjunctionPlusParentPrefix (n := n) (Y := Y)) := by
  intro H K h
  have ho (i : Fin (n + 1)) : H.obj i = K.obj i := by
    apply walkingAdjunctionOrdinalCard_injective .plus Y
    have he := congrArg (walkingAdjunctionOrdinalCard .minus Y)
      (CategoryTheory.Functor.congr_obj h i)
    rw [walkingAdjunctionPlusParentPrefix_card, walkingAdjunctionPlusParentPrefix_card] at he
    omega
  exact (walkingAdjunctionHorizontal_functor_inj .minus .plus Y _ _ H K
    (fun _ => rfl) ho h).2

/-- 概要：実生成射を前置した全長さの実鎖は、各実辺で二番目の点を0へ送らない。
方針：正の長さでは実併合の不在を展開し、長さ0では実辺がないことを使う。
規約：切れ目の回収に渡す全辺の法則。使われ方：Riehl–Verity Lemma 4.1.4の実逆。 -/
lemma walkingAdjunctionPlusParentPrefix_no_one {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n) :
    ∀ k : Fin n, ∀ a : Fin (walkingAdjunctionOrdinalCard .minus Y
      ((walkingAdjunctionPlusParentPrefix H).obj k.castSucc)),
      a.val = 1 → (walkingAdjunctionOrderHom
        ((walkingAdjunctionPlusParentPrefix H).map
          (homOfLE (Fin.castSucc_le_succ k))) a).val ≠ 0 := by
  cases n with
  | zero => intro k; exact Fin.elim0 k
  | succ n =>
    intro k a ha hz
    exact walkingAdjunctionPlusParentPrefix_no_bottom_merge H k ⟨a, ha, hz⟩

/-- 概要：始点plusの実原子に前置した生成射を取り除くと、元の全実関手へ戻る。
方針：前置後の回収の等式と、実前置の全関手の単射性を合わせる。
規約：逆の証人を入力せず、構成したものの往復。使われ方：Riehl–Verity Lemma 4.1.4。 -/
lemma walkingAdjunctionRemoveBottomPrefix_roundtrip {n : ℕ} {Y : WalkingAdjunctionPoint}
    (H : ComposableArrows (walkingAdjunctionHom .plus Y) n)
    (ha : WalkingAdjunctionLevelIsAtomic (X := ⟨.plus⟩) (Y := ⟨Y⟩) H) :
    walkingAdjunctionRemoveBottomPrefix (walkingAdjunctionPlusParentPrefix H)
      (walkingAdjunctionPlusParentPrefix_no_one H)
      (walkingAdjunctionPlusParentPrefix_last_card H ha) = H := by
  apply walkingAdjunctionPlusParentPrefix_injective
  exact walkingAdjunctionRemoveBottomPrefix_prefix _ _ _

end SerrePositivity.InfinityCategories.HA.Monads

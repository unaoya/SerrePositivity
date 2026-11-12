module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceComponents

/-! # 選んだ面からの対象と斉次成分の回収

概要：全ての頂点を覆う選んだ面から、既知の部分集合の対象と射を回収する。
方針：N2 の面による回収を使い、既知であることを集合を避ける選んだ頂点の存在で表す。
規約：HA Proposition 1.3.1.10、HTT §1.2.13。使われ方：N7c の未知六成分以外の入力。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：全頂点を覆う面の族では、各頂点は選んだ頂点の一つとは異なる。
方針：全ての頂点について回避可能な面の存在を条件として記録する。
規約：HA Proposition 1.3.1.10。使われ方：大域対象族を回収するための被覆条件。 -/
def CoversVertices {n : ℕ} (S : Finset (Fin (n + 1))) : Prop :=
  ∀ k, ∃ j ∈ S, j ≠ k

/-- 概要：覆われる各頂点は選んだ面の和の零単体になる。
方針：その頂点と異なる選んだ面を使い、定値写像の単体を作る。
規約：HA Proposition 1.3.1.10。使われ方：共通の対象族の定義。 -/
def vertexCell {n : ℕ} (S : Finset (Fin (n + 1))) (hS : CoversVertices S)
    (k : Fin (n + 1)) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region.{u} S : SSet) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.cell S (SimplexCategory.const ⦋0⦌ ⦋n⦌ k) (hS k).choose (hS k).choose_spec.1
    (fun _ => (hS k).choose_spec.2.symm)

/-- 概要：面の頂点への制限は対応する大域頂点の単体。
方針：部分型の外延性で定値順序写像を比較する。
規約：HA Proposition 1.3.1.10。使われ方：面と大域対象の同定。 -/
lemma map_const_face {n : ℕ} (S : Finset (Fin (n + 2))) (hS : CoversVertices S)
    (j : Fin (n + 2)) (hjS : j ∈ S) (k : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region.{u} S : SSet).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ k).op (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS) =
      vertexCell S hS (j.succAbove k) := by
  apply Subtype.ext
  apply SSet.stdSimplex.objEquiv.injective
  ext x : 3
  rfl

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：部分境界の各頂点は dg 圏の対象を定める。
方針：零単体の像の唯一の対象を評価する。
規約：HA Proposition 1.3.1.10。使われ方：充填する単体の対象族。 -/
def vertexObj {n : ℕ} (S : Finset (Fin (n + 3))) (hS : CoversVertices S)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (k : Fin (n + 3)) : D :=
  (σ.app _ (vertexCell S hS k)).obj 0

/-- 概要：選んだ面の各対象は、部分境界から回収した同じ頂点の対象と一致する。
方針：定値零単体への制限で自然性を評価し、面の頂点の計算を使う。
規約：HA Proposition 1.3.1.10。使われ方：面から回収する射の両端を共通の対象族に移す。 -/
lemma face_obj {n : ℕ} (S : Finset (Fin (n + 3))) (hS : CoversVertices S)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 3)) (hjS : j ∈ S) (k : Fin (n + 2)) :
    (σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).obj k = vertexObj S hS σ (j.succAbove k) := by
  have h := congrArg (fun f => (f (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).obj 0)
    (σ.naturality (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ k).op)
  simp only [CategoryTheory.comp_apply] at h
  exact h.symm

/-- 概要：面の斉次成分を、回収した共通の対象族の間の射として読む。
方針：各面の対象と頂点の対象の等式で両端を移送する。
規約：HA Proposition 1.3.1.10。使われ方：既知成分の回収。 -/
def componentOnFace {n : ℕ} (S : Finset (Fin (n + 3))) (hS : CoversVertices S)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 3)) (hjS : j ∈ S) (J : Finset (Fin (n + 2)))
    (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    GradedHom A (vertexObj S hS σ (j.succAbove a)) (vertexObj S hS σ (j.succAbove b)) k :=
  cast (by rw [face_obj S hS σ j hjS a, face_obj S hS σ j hjS b])
    ((σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).hom J a b k hJ ha hb hk)

/-- 概要：共通の対象族へ移送した成分は、元の面の成分と異種等号で一致する。
方針：cast は元の値と異種等号で等しい。
規約：HA Proposition 1.3.1.10。使われ方：面との一致を検証する際の移送の消去。 -/
lemma componentOnFace_heq {n : ℕ} (S : Finset (Fin (n + 3))) (hS : CoversVertices S)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 3)) (hjS : j ∈ S) (J : Finset (Fin (n + 2)))
    (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    HEq (componentOnFace S hS σ j hjS J a b k hJ ha hb hk)
      ((σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).hom J a b k hJ ha hb hk) := cast_heq _ _

/-- 概要：選んだ面に含まれる部分集合の斉次成分を部分境界の面から回収する。
方針：その集合を含む面を選び、埋め込みの逆像で添字と次数を移し、両端を共通の対象へ移す。
規約：HA Proposition 1.3.1.10。使われ方：充填する単体の既知の射族。
未知成分の方程式はここでは主張しない。 -/
def recoverHom {n : ℕ} (S : Finset (Fin (n + 3))) (hS : CoversVertices S)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (I : Finset (Fin (n + 3))) (a b : Fin (n + 3)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hknown : ∃ j ∈ S, j ∉ I) :
    GradedHom A (vertexObj S hS σ a) (vertexObj S hS σ b) k := by
  let j := hknown.choose
  have hjS : j ∈ S := hknown.choose_spec.1
  have hj : j ∉ I := hknown.choose_spec.2
  have hamin : IsLeast (I : Set (Fin (n + 3))) a := by
    rw [ha]; exact I.isLeast_min' _
  have hbmax : IsGreatest (I : Set (Fin (n + 3))) b := by
    rw [hb]; exact I.isGreatest_max' _
  have hexA : ∃ a', j.succAbove a' = a :=
    Fin.exists_succAbove_eq (fun he => hj (he ▸ hamin.1))
  have hexB : ∃ b', j.succAbove b' = b :=
    Fin.exists_succAbove_eq (fun he => hj (he ▸ hbmax.1))
  let a' := hexA.choose
  let b' := hexB.choose
  have ha' : j.succAbove a' = a := hexA.choose_spec
  have hb' : j.succAbove b' = b := hexB.choose_spec
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hcard : J.card = I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.card_preimage I j hj
  have hJ : 2 ≤ J.card := by omega
  have haMem : a' ∈ J := by simpa only [J, Finset.mem_preimage, Finset.mem_coe, ha'] using hamin.1
  have hbMem : b' ∈ J := by simpa only [J, Finset.mem_preimage, Finset.mem_coe, hb'] using hbmax.1
  have hMin : IsLeast (J : Set (Fin (n + 2))) a' := by
    refine ⟨haMem, ?_⟩
    intro x hx
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_le_iff (f := j.succAbove) j.succAboveOrderEmb.monotone
      j.succAboveOrderEmb.injective.injOn haMem hx).mp
    rw [ha']
    exact hamin.2 (Finset.mem_preimage.mp hx)
  have hMax : IsGreatest (J : Set (Fin (n + 2))) b' := by
    refine ⟨hbMem, ?_⟩
    intro x hx
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_le_iff (f := j.succAbove) j.succAboveOrderEmb.monotone
      j.succAboveOrderEmb.injective.injOn hx hbMem).mp
    rw [hb']
    exact hbmax.2 (Finset.mem_preimage.mp hx)
  let f := componentOnFace S hS σ j hjS J a' b' k hJ
    (hMin.unique (J.isLeast_min' _)) (hMax.unique (J.isGreatest_max' _))
    (by rw [hcard]; exact hk)
  exact cast (by rw [ha', hb']) f

/-- 概要：回収した既知成分は、その集合を含む任意の選んだ面の成分と異種等号で一致する。
方針：回収時の二つの移送を異種等号で外し、共通の集合を持つ二面の成分の一致を使う。
規約：HA Proposition 1.3.1.10。使われ方：回収の選択独立性と面への制限の検証。 -/
lemma recoverHom_heq_face {n : ℕ} (S : Finset (Fin (n + 3))) (hS : CoversVertices S)
    (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region S : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (I : Finset (Fin (n + 3))) (a b : Fin (n + 3)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ))
    (hknown : ∃ j ∈ S, j ∉ I)
    (j : Fin (n + 3)) (hjS : j ∈ S) (J : Finset (Fin (n + 2)))
    (c d : Fin (n + 2)) (hJ : 2 ≤ J.card)
    (hc : c = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hd : d = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk' : k = 2 - (J.card : ℤ)) (hImage : J.image j.succAbove = I) :
    HEq (recoverHom S hS σ I a b k hI ha hb hk hknown)
      ((σ.app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face S j hjS)).hom J c d k hJ hc hd hk') := by
  unfold recoverHom
  refine (cast_heq _ _).trans ?_
  refine (componentOnFace_heq S hS σ _ _ _ _ _ _ _ _ _ _).trans ?_
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.face_hom_heq S σ
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I _ hknown.choose_spec.2).trans
    hImage.symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData

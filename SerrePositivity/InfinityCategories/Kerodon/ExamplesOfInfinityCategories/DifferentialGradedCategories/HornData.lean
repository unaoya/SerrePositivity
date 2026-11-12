module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornFaces

/-! # dg nerve のホーンから回収する対象

概要：ホーンの頂点から対象を回収し、各面の対象と一致することを示す。
方針：面の定値零単体への制限とホーンからの写像の自然性を使う。
規約：HA Proposition 1.3.1.10。使われ方：既知の斉次成分の端点の対象の同定。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

/-- 概要：ホーンの面の一頂点への制限は、その頂点に集中する零単体。
方針：標準単体の反変写像を評価し、面の順序埋め込みで頂点を移す。
規約：HA Proposition 1.3.1.10。使われ方：ホーンの面と頂点の対象の同定。 -/
lemma map_const_face {n : ℕ} (i j : Fin (n + 3)) (hji : j ≠ i) (k : Fin (n + 2)) :
    (Λ[n + 2, i] : SSet.{u}).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ k).op
        (SSet.horn.face i j hji) =
      SSet.horn.const n i (j.succAbove k) (op ⦋0⦌) := by
  apply Subtype.ext
  apply SSet.stdSimplex.objEquiv.injective
  ext x : 3
  rfl

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：ホーンの各頂点は dg 圏の対象を定める。
方針：ホーンの定値零単体を与え、その像の唯一の頂点を評価する。
規約：HA Proposition 1.3.1.10。使われ方：充填する単体の対象族。 -/
def vertexObj {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (k : Fin (n + 3)) : D :=
  (σ.app _ (SSet.horn.const n i k (op ⦋0⦌))).obj 0

/-- 概要：利用可能な面の各対象は、ホーンから回収した同じ頂点の対象と一致する。
方針：定値零単体への制限で自然性を評価し、面の頂点の計算を使う。
規約：HA Proposition 1.3.1.10。使われ方：面から回収する射の両端を共通の対象族に移す。 -/
lemma face_obj {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 3)) (hji : j ≠ i) (k : Fin (n + 2)) :
    (σ.app _ (SSet.horn.face i j hji)).obj k = vertexObj σ (j.succAbove k) := by
  have h := congrArg (fun f => (f (SSet.horn.face i j hji)).obj 0)
    (σ.naturality (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ k).op)
  simp only [CategoryTheory.comp_apply, map_const_face] at h
  exact h.symm

/-- 概要：面の斉次成分を、回収した共通の対象族の間の射として読む。
方針：各面の対象と頂点の対象の等式で両端を移送する。
規約：HA Proposition 1.3.1.10。使われ方：既知成分の回収。 -/
def componentOnFace {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 3)) (hji : j ≠ i) (J : Finset (Fin (n + 2)))
    (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    GradedHom A (vertexObj σ (j.succAbove a)) (vertexObj σ (j.succAbove b)) k :=
  cast (by rw [face_obj σ j hji a, face_obj σ j hji b])
    ((σ.app _ (SSet.horn.face i j hji)).hom J a b k hJ ha hb hk)

/-- 概要：共通の対象族へ移送した成分は、元の面の成分と異種等号で一致する。
方針：cast は元の値と異種等号で等しい。
規約：HA Proposition 1.3.1.10。使われ方：面との一致を検証する際の移送の消去。 -/
lemma componentOnFace_heq {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (j : Fin (n + 3)) (hji : j ≠ i) (J : Finset (Fin (n + 2)))
    (a b : Fin (n + 2)) (k : ℤ) (hJ : 2 ≤ J.card)
    (ha : a = J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)) (hb : b = J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ))
    (hk : k = 2 - (J.card : ℤ)) :
    HEq (componentOnFace σ j hji J a b k hJ ha hb hk)
      ((σ.app _ (SSet.horn.face i j hji)).hom J a b k hJ ha hb hk) := cast_heq _ _

/-- 概要：全体集合と欠けた面以外の部分集合の斉次成分をホーンの面から回収する。
方針：その集合を含む面を選び、埋め込みの逆像で添字と次数を移し、両端を共通の対象へ移す。
規約：HA Proposition 1.3.1.10。使われ方：充填する単体の既知の射族。
この定義だけでは全ての制限の整合性と未知の二成分の方程式は主張しない。 -/
def recoverHom {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (I : Finset (Fin (n + 3))) (a b : Fin (n + 3)) (k : ℤ) (hI : 2 ≤ I.card)
    (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - (I.card : ℤ))
    (hfull : I ≠ Finset.univ) (hmissing : I ≠ Finset.univ.erase i) :
    GradedHom A (vertexObj σ a) (vertexObj σ b) k := by
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace I i hfull hmissing
  have hji : j ≠ i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_ne I i hfull hmissing
  have hj : j ∉ I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_notMem I i hfull hmissing
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
  let f := componentOnFace σ j hji J a' b' k hJ
    (hMin.unique (J.isLeast_min' _)) (hMax.unique (J.isGreatest_max' _))
    (by rw [hcard]; exact hk)
  exact cast (by rw [ha', hb']) f

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData

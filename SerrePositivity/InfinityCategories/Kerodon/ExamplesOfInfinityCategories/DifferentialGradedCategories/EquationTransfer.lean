module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Replace

/-! # ホーン面からの方程式の移送

概要：全ての既知の面への制限が元の単体と一致するデータは、既知の集合で方程式を満たす。
方針：集合を含む面を選び、単射による成分と右辺の移送を使う。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面の成分の補正後の既知方程式の保存。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory Opposite DifferentialGraded
open scoped _root_.Simplicial

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

namespace SimplexData

/-- 概要：一つの部分集合について、その全端点・次数で単体の方程式が成り立つという命題。
方針：従来の単体の方程式を部分集合だけに関する述語として束ねる。
規約：HA Construction 1.3.1.6。使われ方：面の像や未知成分の置換の方程式の記述。 -/
def Equation {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n) (I : Finset (Fin (n + 1))) : Prop :=
  ∀ a b k hI ha hb hk,
    differential A (s.hom I a b k hI ha hb hk) = s.rhs I a b k hI ha hb hk

/-- 概要：データの単射による制限が単体なら、元のデータはその像の集合で方程式を満たす。
方針：最小元と最大元を単調写像で写し、制限の方程式を移送する。
規約：HA Proposition 1.3.1.10。使われ方：既知の面の方程式を大域の集合に戻す。 -/
lemma equation_image_of_pullback {m n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D n)
    (α : Fin (m + 1) →o Fin (n + 1)) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D m)
    (h : s.pullback α = t.toSimplexData) (J : Finset (Fin (m + 1)))
    (hi : Set.InjOn α (J : Set (Fin (m + 1)))) : s.Equation (J.image α) := by
  intro a b k hI ha hb hk
  have hcard : (J.image α).card = J.card := Finset.card_image_of_injOn hi
  have hJ : 2 ≤ J.card := by omega
  have hkJ : k = 2 - (J.card : ℤ) := by rwa [hcard] at hk
  let a' := J.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  let b' := J.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hJ)
  have ha' : α a' = a := by
    rw [ha]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_min α.monotone (J.isLeast_min' _) _
  have hb' : α b' = b := by
    rw [hb]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.image_max α.monotone (J.isGreatest_max' _) _
  have hh := t.equation J a' b' k hJ rfl rfl hkJ
  rw [← h] at hh
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _ hi,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _ hi] at hh
  cases ha'
  cases hb'
  exact hh

end SimplexData

namespace HornData

/-- 概要：既知の全ての面に一致するデータは、未知の二集合以外で方程式を満たす。
方針：集合を含む利用可能な面の存在と、像の集合の方程式の移送を使う。
規約：HA Proposition 1.3.1.10。使われ方：補正後のデータの既知方程式を一度に検証する。 -/
lemma equation_of_faces {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2))
    (hfaces : ∀ j (hji : j ≠ i), s.pullback j.succAboveOrderEmb.toOrderHom =
      (σ.app _ (SSet.horn.face i j hji)).toSimplexData)
    (I : Finset (Fin (n + 3))) (hfull : I ≠ Finset.univ)
    (hmissing : I ≠ Finset.univ.erase i) : s.Equation I := by
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace I i hfull hmissing
  have hji : j ≠ i := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_ne I i hfull hmissing
  have hj : j ∉ I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coveringFace_notMem I i hfull hmissing
  let J := I.preimage j.succAbove j.succAboveOrderEmb.injective.injOn
  have hh := s.equation_image_of_pullback j.succAboveOrderEmb.toOrderHom
    (σ.app _ (SSet.horn.face i j hji)) (hfaces j hji) J j.succAboveOrderEmb.injective.injOn
  have hImage : J.image j.succAboveOrderEmb.toOrderHom = I := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.image_preimage I j hj
  simpa only [hImage] using hh

/-- 概要：欠けた面の成分を任意に置き換えても、全ての利用可能な面への制限は保存される。
方針：各面が飛ばす頂点は欠けた面の集合に属し、その像からは避けられることを使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位方程式から解いた成分を入れる準備。 -/
lemma replace_missing_pullback_face {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (f : ∀ a b k (hM : 2 ≤ (Finset.univ.erase i).card),
      a = (Finset.univ.erase i).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      b = (Finset.univ.erase i).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      k = 2 - ((Finset.univ.erase i).card : ℤ) →
      GradedHom A (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.vertexObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.vertexObj σ b) k)
    (j : Fin (n + 3)) (hji : j ≠ i) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).replace (Finset.univ.erase i) f).pullback j.succAboveOrderEmb.toOrderHom =
      (σ.app _ (SSet.horn.face i j hji)).toSimplexData := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_pullback_of_omits _ _ _ _ j
    (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) (fun x => Fin.succAbove_ne j x)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ j hji

/-- 概要：欠けた面の成分を任意に置き換えたデータも、既知の全ての集合で方程式を満たす。
方針：置換後も既知の面への制限が保存されることから、面による方程式の検証を使う。
規約：HA Proposition 1.3.1.10。使われ方：未知の二方程式だけを個別に証明すればよいこと。 -/
lemma replace_missing_equation {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (f : ∀ a b k (hM : 2 ≤ (Finset.univ.erase i).card),
      a = (Finset.univ.erase i).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      b = (Finset.univ.erase i).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hM) →
      k = 2 - ((Finset.univ.erase i).card : ℤ) →
      GradedHom A (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.vertexObj σ a) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.vertexObj σ b) k)
    (I : Finset (Fin (n + 3))) (hfull : I ≠ Finset.univ)
    (hmissing : I ≠ Finset.univ.erase i) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).replace (Finset.univ.erase i) f).Equation I :=
  equation_of_faces σ _ (replace_missing_pullback_face σ f) I hfull hmissing

end HornData

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

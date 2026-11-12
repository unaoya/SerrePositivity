module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.TopCorrection

/-! # dg nerve の内部ホーンの充填候補

概要：既知成分から、最上位方程式を満たす単体データを構成する。
方針：全体成分を零のままにし、欠けた面の成分から符号付きの最上位右辺を引く。
規約：HA Proposition 1.3.1.10。使われ方：欠けた面自身の方程式を残差恒等式で検証する。
この段階ではデータだけであり、充填単体の存在や quasicategory 性はまだ主張しない。

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

/-- 概要：頂点全体の最小元は零。
方針：零が全体集合の最小元であることから最小元の一意性を使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位成分と欠けた面の共通の始点。 -/
lemma univ_min_zero (n : ℕ) (h : (Finset.univ : Finset (Fin (n + 3))).Nonempty) :
    (0 : Fin (n + 3)) = Finset.univ.min' h :=
  (show IsLeast ((Finset.univ : Finset (Fin (n + 3))) : Set (Fin (n + 3))) 0 from
    ⟨Finset.mem_univ _, fun x _ => Fin.zero_le x⟩).unique (Finset.univ.isLeast_min' h)

/-- 概要：頂点全体の最大元は最後の頂点。
方針：最後の頂点が全体集合の最大元であることから最大元の一意性を使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位成分と欠けた面の共通の終点。 -/
lemma univ_max_last (n : ℕ) (h : (Finset.univ : Finset (Fin (n + 3))).Nonempty) :
    Fin.last (n + 2) = Finset.univ.max' h :=
  (show IsGreatest ((Finset.univ : Finset (Fin (n + 3))) : Set (Fin (n + 3)))
      (Fin.last (n + 2)) from
    ⟨Finset.mem_univ _, fun x _ => Fin.le_last x⟩).unique (Finset.univ.isGreatest_max' h)

/-- 概要：内部ホーンから、最上位成分が零で最上位方程式を満たすデータを作る。
方針：既知成分を回収し、内部点を削除した成分に最上位右辺を消す補正を適用する。
規約：HA Proposition 1.3.1.10。使われ方：残る欠けた面の方程式を検証する充填候補。 -/
def fillerData {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).solveTop Finset.univ 0 (Fin.last (n + 2))
    (2 - ((Finset.univ : Finset (Fin (n + 3))).card : ℤ))
    (by simp) (univ_min_zero n _) (univ_max_last n _) rfl i (Finset.mem_univ i) h0 hlast

/-- 概要：充填候補の全ての既知の面への制限は元のホーン面のデータに等しい。
方針：欠けた面の成分の置換は利用可能な面への制限を変えないことを使う。
規約：HA Proposition 1.3.1.10。使われ方：最終的なホーンの貼合せと既知方程式の保存。 -/
lemma fillerData_pullback_face {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2)) (j : Fin (n + 3)) (hji : j ≠ i) :
    (fillerData σ h0 hlast).pullback j.succAboveOrderEmb.toOrderHom =
      (σ.app _ (SSet.horn.face i j hji)).toSimplexData := by
  unfold fillerData _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.solveTop
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.replace_missing_pullback_face σ _ j hji

/-- 概要：充填候補は既知の全ての部分集合で単体の方程式を満たす。
方針：各既知の面への制限が元の単体であることから方程式を移送する。
規約：HA Proposition 1.3.1.10。使われ方：充填候補で未検証の方程式を限定する。 -/
lemma fillerData_known_equation {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2))
    (I : Finset (Fin (n + 3))) (hfull : I ≠ Finset.univ)
    (hmissing : I ≠ Finset.univ.erase i) : (fillerData σ h0 hlast).Equation I :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornData.equation_of_faces σ _ (fillerData_pullback_face σ h0 hlast) I hfull hmissing

/-- 概要：充填候補の最上位成分は零。
方針：削除集合の置換は全体集合を変えず、既知データの全体成分は零であることを使う。
規約：HA Proposition 1.3.1.10。使われ方：最上位方程式の左辺の検証。 -/
lemma fillerData_top_zero {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2))
    (a b : Fin (n + 3)) (k : ℤ) (hI : 2 ≤ (Finset.univ : Finset (Fin (n + 3))).card)
    (ha : a = Finset.univ.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = Finset.univ.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hk : k = 2 - ((Finset.univ : Finset (Fin (n + 3))).card : ℤ)) :
    (fillerData σ h0 hlast).hom Finset.univ a b k hI ha hb hk = 0 := by
  have hne : (Finset.univ : Finset (Fin (n + 3))) ≠ Finset.univ.erase i := by
    intro h
    have hm : i ∈ (Finset.univ : Finset (Fin (n + 3))) := Finset.mem_univ i
    rw [h] at hm
    exact Finset.notMem_erase i Finset.univ hm
  unfold fillerData _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.solveTop
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.replace_hom_of_ne _ _ _ _ _ _ _ _ _ _ _ hne]
  simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData]

/-- 概要：充填候補は最上位集合で単体の方程式を満たす。
方針：最上位成分は零であり、補正により右辺も零になる。
規約：HA Proposition 1.3.1.10。使われ方：残る方程式が欠けた面自身だけであること。 -/
lemma fillerData_top_equation {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2)) :
    (fillerData σ h0 hlast).Equation Finset.univ := by
  intro a b k hI ha hb hk
  have ha0 : a = 0 := ha.trans (univ_min_zero n _).symm
  have hbLast : b = Fin.last (n + 2) := hb.trans (univ_max_last n _).symm
  subst ha0
  subst hbLast
  have hrhs : (fillerData σ h0 hlast).rhs Finset.univ 0 (Fin.last (n + 2)) k hI ha hb hk = 0 := by
    subst k
    unfold fillerData
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.rhs_solveTop _ _ _ _ _ _ _ _ _ _ _ _ _
  rw [fillerData_top_zero σ h0 hlast _ _ _ _ _ _ _, hrhs]
  simp [differential]

/-- 概要：充填候補の欠けた面の方程式が成り立てば、そのデータは実際の単体となる。
方針：全体集合・欠けた面・既知集合の三場合に分け、既に示した方程式を適用する。
規約：HA Proposition 1.3.1.10。使われ方：残差恒等式から最後の方程式を得た後の単体の構成。
欠けた面の方程式はこの定義の明示的な前提であり、ここではまだ証明していない。 -/
def fillerOfMissingEquation {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2))
    (hmissing : (fillerData σ h0 hlast).Equation (Finset.univ.erase i)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 2) where
  toSimplexData := fillerData σ h0 hlast
  equation I a b k hI ha hb hk := by
    by_cases hfull : I = Finset.univ
    · subst I
      exact fillerData_top_equation σ h0 hlast a b k hI ha hb hk
    · by_cases hm : I = Finset.univ.erase i
      · subst I
        exact hmissing a b k hI ha hb hk
      · exact fillerData_known_equation σ h0 hlast I hfull hm a b k hI ha hb hk

/-- 概要：欠けた面の方程式から作った単体の各既知の面は元のホーン面と一致する。
方針：データの面への制限の等式から、単体の外延性を使う。
規約：HA Proposition 1.3.1.10。使われ方：充填写像のホーンへの制限の計算。 -/
lemma fillerOfMissingEquation_face {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2))
    (hmissing : (fillerData σ h0 hlast).Equation (Finset.univ.erase i))
    (j : Fin (n + 3)) (hji : j ≠ i) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D).δ j (fillerOfMissingEquation σ h0 hlast hmissing) =
      σ.app _ (SSet.horn.face i j hji) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  exact fillerData_pullback_face σ h0 hlast j hji

/-- 概要：欠けた面の方程式が成り立てば、候補単体は元のホーン写像の延長を与える。
方針：米田対応で候補単体を写像にし、各既知の面での一致からホーンの外延性を使う。
規約：HA Proposition 1.3.1.10。使われ方：最後の方程式の証明後のホーン貼合せ。
この定理は前提付きであり、内部ホーンの無条件の充填はまだ与えない。 -/
lemma extensionOfMissingEquation {n : ℕ} {i : Fin (n + 3)}
    (σ : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (h0 : 0 < i) (hlast : i < Fin.last (n + 2))
    (hmissing : (fillerData σ h0 hlast).Equation (Finset.univ.erase i)) :
    ∃ τ : (Δ[n + 2] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D, σ = Λ[n + 2, i].ι ≫ τ := by
  refine ⟨SSet.yonedaEquiv.symm (fillerOfMissingEquation σ h0 hlast hmissing), ?_⟩
  apply SSet.horn.hom_ext
  intro j hji
  rw [← fillerOfMissingEquation_face σ h0 hlast hmissing j hji, NatTrans.comp_app]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CubeEvaluation
public import Mathlib.AlgebraicTopology.SimplicialSet.NerveNondegenerate

/-!
# 退化単体の最上位評価の消滅

概要：標準 Hom の退化単体の最上位成分は零であり、頂点が重複する順序 nerve の像も零となる。
方針：退化写像は全頂点上で単射でないので成分が零になる。順序 nerve の退化判定を使う。
規約：単体集合の任意の射に適用し、線形性は仮定しない。
使われ方：HA 1.3.1.16、Kerodon 2.5.8（Tag 00S0）–2.5.9（Tag 00SC） の shuffle と退化項の消去。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：非単射な単調写像による引き戻しの最上位成分は零である。
方針：全体集合上の非単射性を成分族の引き戻しの消滅条件にする。
規約：次元 m の最上位評価は次数 −m。
使われ方：Kerodon 2.5.8（Tag 00S0） の退化単体の正規化における消滅。 -/
lemma standardTopEval_pullback_zero {m n : ℕ} (α : Fin (m + 1) →o Fin (n + 1))
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) (hα : ¬ Function.Injective α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y m (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α f) = 0 := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α f).val.component Finset.univ (-(m : ℤ))
    Finset.univ_nonempty (by simp) = 0
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_not_inj
  simpa only [Finset.coe_univ, Set.injOn_univ] using hα

/-- 概要：標準 Hom の一段の退化の最上位成分は零である。
方針：退化写像が隣接する二点を同じ点へ送ることを使う。
規約：零単体の退化で得た一次単体も含む。
使われ方：HA 1.3.1.16 の潰れた旗の評価。 -/
lemma standardTopEval_sigma_zero {n : ℕ} (i : Fin (n + 1))
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y (n + 1) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y).σ i f) = 0 := by
  apply standardTopEval_pullback_zero
  intro hi
  have h := hi (show (SimplexCategory.σ i).toOrderHom i.castSucc =
      (SimplexCategory.σ i).toOrderHom i.succ by
        change i.predAbove i.castSucc = i.predAbove i.succ
        simp)
  exact (ne_of_lt i.castSucc_lt_succ) h

/-- 概要：単体集合の退化単体を標準 Hom に送ると最上位評価は零になる。
方針：退化単体を一段の退化として表し、射の自然性で退化を移す。
規約：始域には任意の単体集合を許す。
使われ方：Kerodon 2.5.9（Tag 00SC） の旗の退化による不要項の消去。 -/
lemma standardTopEval_map_degenerate_zero {X : SSet.{u}} {n : ℕ}
    (φ : X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) (s : X _⦋n⦌)
    (hs : s ∈ X.degenerate n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y n (φ.app _ s) = 0 := by
  cases n with
  | zero =>
    simp only [SSet.degenerate_zero, Set.mem_empty_iff_false] at hs
  | succ n =>
    rw [SSet.degenerate_eq_iUnion_range_σ] at hs
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hs
    have h := φ.naturality_apply (SimplexCategory.σ i).op t
    exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y (n + 1)) h).trans
      (standardTopEval_sigma_zero i _)

/-- 概要：順序 nerve の頂点写像が非単射なら、その像の最上位評価は零である。
方針：順序 nerve の非退化単体が頂点上単射であるという判定を使う。
規約：反対称性を持つ順序の nerve を使う。
使われ方：HA 1.3.1.16 の座標を忘れた旗の評価の消滅。 -/
lemma standardTopEval_nerve_zero {P : Type u} [PartialOrder P] {n : ℕ}
    (φ : nerve P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) (s : (nerve P) _⦋n⦌)
    (hs : ¬ Function.Injective s.obj) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y n (φ.app _ s) = 0 := by
  apply standardTopEval_map_degenerate_zero
  rw [SSet.mem_degenerate_iff_notMem_nonDegenerate,
    PartialOrder.mem_nerve_nonDegenerate_iff_injective]
  exact hs

/-- 概要：単射な引き戻しの最上位評価は像の頂点集合の成分である。
方針：全体集合上の単射な引き戻しの成分を計算する。
規約：像の集合の濃度は元の次元で決まる。
使われ方：Kerodon 2.5.8（Tag 00S0） の接頭・接尾集合の成分を小さい単体の評価へ移す。 -/
lemma standardTopEval_pullback_injective {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y n)
    (hα : Function.Injective α) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y m (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α f) =
      f.val.component (Finset.univ.image α) (-(m : ℤ))
        (Finset.univ_nonempty.image α)
        (by rw [Finset.card_image_of_injective _ hα]; simp) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback α f).val.component Finset.univ (-(m : ℤ))
    Finset.univ_nonempty (by simp) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj α f.val _ _ _ _ hα.injOn

/-- 概要：選んだ頂点集合で順序 nerve の頂点が重複すれば、その像の成分は零である。
方針：単射な頂点選択で引き戻し、頂点の重複による最上位評価の消滅を使う。
規約：成分の次数を明示し、像の頂点集合の濃度で指定する。
使われ方：HA 1.3.1.16 の AW の接頭・接尾成分の退化項の消去。 -/
lemma standardComponent_nerve_zero {P : Type u} [PartialOrder P] {m n : ℕ}
    (φ : nerve P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) (s : (nerve P) _⦋n⦌)
    (α : Fin (m + 1) →o Fin (n + 1)) (hα : Function.Injective α)
    (hs : ¬ Function.Injective (fun j ↦ s.obj (α j))) (k : ℤ)
    (hk : k = 1 - ((Finset.univ.image α).card : ℤ)) :
    (φ.app _ s).val.component (Finset.univ.image α) k
      (Finset.univ_nonempty.image α) hk = 0 := by
  have hp : k = -(m : ℤ) := by
    rw [Finset.card_image_of_injective _ hα] at hk
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one] at hk
    omega
  subst hp
  refine (standardTopEval_pullback_injective α (φ.app _ s) hα).symm.trans ?_
  refine (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardTopEval (R := R) x y m)
    (φ.naturality_apply (SimplexCategory.mkHom α).op s).symm).trans ?_
  exact standardTopEval_nerve_zero φ ((nerve P).map (SimplexCategory.mkHom α).op s) hs

/-- 概要：順序 nerve の単体の像は頂点が重複する非空集合の成分で零となる。
方針：有限集合を昇順に番号付けし、その単射な選択写像で引き戻す。
規約：次数 k は集合の濃度で指定し、特定の次数表示には固定しない。
使われ方：Kerodon 2.5.8（Tag 00S0） の AW 成分の退化項の判定。 -/
lemma standardComponent_nerve_zero_of_not_injOn {P : Type u} [PartialOrder P] {n : ℕ}
    (φ : nerve P ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomSpace (R := R) x y) (s : (nerve P) _⦋n⦌)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ))
    (hs : ¬ Set.InjOn s.obj (J : Set (Fin (n + 1)))) :
    (φ.app _ s).val.component J k hJ hk = 0 := by
  classical
  let m := J.card - 1
  have hc : J.card = m + 1 := by have := Finset.card_pos.mpr hJ; omega
  let e := J.orderIsoOfFin hc
  let α := (J.orderEmbOfFin hc).toOrderHom
  have hα : Function.Injective α := (J.orderEmbOfFin hc).injective
  have he : Finset.univ.image α = J := by
    ext a
    constructor
    · intro ha
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
      exact (e j).property
    · intro ha
      exact Finset.mem_image.mpr ⟨e.symm ⟨a, ha⟩, Finset.mem_univ _,
        congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)⟩
  have hs' : ¬ Function.Injective (fun j ↦ s.obj (α j)) := by
    intro hinj
    apply hs
    intro a ha b hb hab
    have ha' : α (e.symm ⟨a, ha⟩) = a :=
      congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩)
    have hb' : α (e.symm ⟨b, hb⟩) = b :=
      congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)
    have h := hinj (show s.obj (α (e.symm ⟨a, ha⟩)) = s.obj (α (e.symm ⟨b, hb⟩)) by
      rw [ha', hb']; exact hab)
    exact congrArg Subtype.val (e.symm.injective h)
  have h := standardComponent_nerve_zero φ s α hα hs' k (by rw [he]; exact hk)
  simpa only [he] using h

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

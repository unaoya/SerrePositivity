module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.PairingHorns
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：セルごとの充填から部分複体上の射を一段延長する補題。
方針：各セルの充填を余積に束ね、pushout の普遍性で貼り合わせる。
規約：充填条件は各段階の既存の射に依存してよい。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の外側ホーンを含む prism のセル分解。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe w t v u
open CategoryTheory Limits HomotopicalAlgebra SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：貼り付ける各セルに充填があれば、射を貼り付け後の対象へ延長できる。
方針：選んだ充填を余積の普遍性で束ねて pushout から射を得る。
規約：特定の既存の射 f の延長を扱い、全ての射に対する rlp は要求しない。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） のセルごとの Joyal の定理の適用。 -/
lemma attachCells_exists_extension {C : Type u} [Category.{v} C]
    {I : Type w} {A B : I → C} {g : ∀ i, A i ⟶ B i}
    {X Y E : C} {j : X ⟶ Y} (c : AttachCells.{t} g j) (f : X ⟶ E)
    (h : ∀ i : c.ι, ∃ F : B (c.π i) ⟶ E,
      g (c.π i) ≫ F = c.cofan₁.inj i ≫ c.g₁ ≫ f) :
    ∃ F : Y ⟶ E, j ≫ F = f := by
  classical
  choose L hL using h
  let b := c.isColimit₂.desc (Cofan.mk E L)
  have hb (i : c.ι) : c.cofan₂.inj i ≫ b = L i := c.isColimit₂.fac _ ⟨i⟩
  have hw : c.g₁ ≫ f = c.m ≫ b := by
    apply Cofan.IsColimit.hom_ext c.isColimit₁
    intro i
    rw [← Category.assoc (c.cofan₁.inj i) c.m b, c.hm, Category.assoc, hb]
    exact (hL i).symm
  exact ⟨c.isPushout.desc f b hw, c.isPushout.inl_desc f b hw⟩

/-- 概要：pairing の階数による filtration の一段をセルごとの充填で延長する。
方針：その階数のホーンを全て貼り付ける pushout の普遍性を使う。
規約：元の部分複体上の射との一致を保存する。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の prism の段階的延長。 -/
lemma pairing_filtration_exists_extension {X E : SSet.{u}} {A : X.Subcomplex}
    {P : A.Pairing} [P.IsProper] (r : P.RankFunction ℕ) (a : (A : SSet.{u}) ⟶ E)
    (n : ℕ) (g : (r.filtration n : SSet.{u}) ⟶ E)
    (hg : Subcomplex.homOfLE (r.le_filtration n) ≫ g = a)
    (h : ∀ c : r.Cell n, ∃ F : (Δ[c.dim + 1] : SSet.{u}) ⟶ E,
      c.horn.ι ≫ F = c.mapHorn ≫ g) :
    ∃ g' : (r.filtration (n + 1) : SSet.{u}) ⟶ E,
      Subcomplex.homOfLE (r.filtration_monotone (Nat.le_succ n)) ≫ g' = g ∧
        Subcomplex.homOfLE (r.le_filtration (n + 1)) ≫ g' = a := by
  have hc (c : (r.relativeCellComplex.attachCells n (not_isMax n)).ι) :
      ∃ F : (Δ[c.dim + 1] : SSet.{u}) ⟶ E,
        c.horn.ι ≫ F =
          (r.relativeCellComplex.attachCells n (not_isMax n)).cofan₁.inj c ≫
            (r.relativeCellComplex.attachCells n (not_isMax n)).g₁ ≫ g := by
    obtain ⟨F, hF⟩ := h c
    refine ⟨F, ?_⟩
    change c.horn.ι ≫ F = c.ιSigmaHorn ≫ r.t n ≫ g
    rw [← Category.assoc, c.ι_t]
    exact hF
  obtain ⟨g', hg'⟩ := attachCells_exists_extension
    (r.relativeCellComplex.attachCells n (not_isMax n)) g hc
  change Subcomplex.homOfLE (r.filtration_monotone (Nat.le_succ n)) ≫ g' = g at hg'
  refine ⟨g', hg', ?_⟩
  have he : Subcomplex.homOfLE (r.le_filtration (n + 1)) =
      Subcomplex.homOfLE (r.le_filtration n) ≫
        Subcomplex.homOfLE (r.filtration_monotone (Nat.le_succ n)) := rfl
  rw [he, Category.assoc, hg', hg]

/-- 概要：正則 pairing の各段階でセルを充填できれば全体へ射を延長できる。
方針：自然数階数の filtration を再帰的に延長し、余極限で射を束ねる。
規約：充填の仮定は元の部分複体上の射との一致を仮定してよい。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の可逆な端の辺を持つ prism。 -/
lemma pairing_exists_extension {X E : SSet.{u}} {A : X.Subcomplex}
    (P : A.Pairing) [P.IsRegular] (a : (A : SSet.{u}) ⟶ E)
    (h : ∀ (n : ℕ) (g : (P.rankFunction.filtration n : SSet.{u}) ⟶ E),
      Subcomplex.homOfLE (P.rankFunction.le_filtration n) ≫ g = a →
      ∀ c : P.rankFunction.Cell n, ∃ F : (Δ[c.dim + 1] : SSet.{u}) ⟶ E,
        c.horn.ι ≫ F = c.mapHorn ≫ g) :
    ∃ F : X ⟶ E, A.ι ≫ F = a := by
  classical
  let r := P.rankFunction
  let T (n : ℕ) := {g : (r.filtration n : SSet.{u}) ⟶ E //
    Subcomplex.homOfLE (r.le_filtration n) ≫ g = a}
  let e := Subcomplex.eqToIso r.filtration_bot
  let g₀ : T 0 := ⟨e.hom ≫ a, by
    rw [← Category.assoc]
    change (𝟙 (A : SSet.{u})) ≫ a = a
    exact Category.id_comp a⟩
  have hs (n : ℕ) (g : T n) : ∃ g' : T (n + 1),
      Subcomplex.homOfLE (r.filtration_monotone (Nat.le_succ n)) ≫ g'.val = g.val := by
    obtain ⟨g', hg', hbase⟩ := pairing_filtration_exists_extension r a n g.val g.property
      (h n g.val g.property)
    exact ⟨⟨g', hbase⟩, hg'⟩
  let step (n : ℕ) (g : T n) : T (n + 1) := Classical.choose (hs n g)
  let G : ∀ n, T n := fun n ↦ Nat.rec g₀ (fun n g ↦ step n g) n
  have hG (n : ℕ) :
      Subcomplex.homOfLE (r.filtration_monotone (Nat.le_succ n)) ≫ (G (n + 1)).val =
        (G n).val := by
    change Subcomplex.homOfLE (r.filtration_monotone (Nat.le_succ n)) ≫
      (step n (G n)).val = (G n).val
    exact Classical.choose_spec (hs n (G n))
  let c : Cocone r.relativeCellComplex.F :=
    ⟨E, NatTrans.ofSequence (fun n ↦ (G n).val) (fun n ↦ by
      change Subcomplex.homOfLE (r.filtration_monotone (Nat.le_succ n)) ≫
        (G (n + 1)).val = (G n).val ≫ 𝟙 E
      rw [Category.comp_id]
      exact hG n)⟩
  let F := r.relativeCellComplex.isColimit.desc c
  refine ⟨F, ?_⟩
  have hf : (r.filtration 0).ι ≫ F = (G 0).val :=
    r.relativeCellComplex.isColimit.fac c 0
  have he : A.ι = Subcomplex.homOfLE (r.le_filtration 0) ≫ (r.filtration 0).ι := rfl
  rw [he, Category.assoc, hf]
  exact (G 0).property

/-- 概要：pairing core のセルの欠ける面の番号は core の指定番号。
方針：core と型 II の単体の全単射における面の一意性を使う。
規約：階数の選択とは独立。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の prism のセルの番号。 -/
lemma pairingCore_cell_index {X : SSet.{u}} {A : X.Subcomplex}
    (Q : A.PairingCore) [Q.IsProper] (r : Q.pairing.RankFunction ℕ) {n : ℕ}
    (s : Q.ι) (hs : r.rank (Q.equivII s) = n) :
    (show r.Cell n from ⟨Q.equivII s, hs⟩).index = Q.index s := by
  simp only [Subcomplex.Pairing.RankFunction.Cell.index,
    Subcomplex.PairingCore.pairing, Equiv.trans_apply, Equiv.symm_apply_apply]
  exact Q.isUniquelyCodimOneFace_index s

/-- 概要：pairing core のセルの射は core の指定した単体の Yoneda 射。
方針：型 II に対応する型 I の単体の式を使う。
規約：階数の条件の証明には依存しない。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の prism の辺の計算。 -/
lemma pairingCore_cell_map {X : SSet.{u}} {A : X.Subcomplex}
    (Q : A.PairingCore) [Q.IsProper] (r : Q.pairing.RankFunction ℕ) {n : ℕ}
    (s : Q.ι) (hs : r.rank (Q.equivII s) = n) :
    (show r.Cell n from ⟨Q.equivII s, hs⟩).map = SSet.yonedaEquiv.symm (Q.simplex s) := by
  have he : S.mk (SSet.yonedaEquiv
      (show r.Cell n from ⟨Q.equivII s, hs⟩).map) = S.mk (Q.simplex s) := by
    simp only [Subcomplex.Pairing.RankFunction.Cell.map, Equiv.apply_symm_apply]
    change ((Q.pairing.p (Q.equivII s)).val.toS.cast
      (Q.pairing.isUniquelyCodimOneFace (Q.equivII s)).dim_eq) = _
    rw [S.cast_eq_self]
    have hh := congrArg (fun t : Q.pairing.I ↦ t.val.toS) (Q.pairing_p_equivII s)
    exact hh
  apply SSet.yonedaEquiv.injective
  exact (eq_of_heq (S.mk.inj he).2).trans (SSet.yonedaEquiv.apply_symm_apply _).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

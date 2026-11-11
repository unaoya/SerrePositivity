module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NormalizedZero

/-!
# 正規化の微分と成分評価

概要：Moore 正規化の微分を零番目の面として具体化し、最上位成分の微分を計算する。
方針：部分対象の包含で等式を検査し、面の全体集合の像を零番目の面に同定する。
規約：Mathlib の Moore 微分は d₀ で、追加の次数符号を入れない。
使われ方：HA 1.3.1.12、Kerodon 2.5.6（Tag 00QQ） の正規化複体と切断 Hom の比較。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open DifferentialGraded
open scoped _root_.Simplicial

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

/-- 概要：Moore 微分と包含の合成は元の単体的対象の零番目の面である。
方針：正規化の微分の因子分解を包含で戻す。
規約：任意の単体的加群と全次数で成立する。
使われ方：HA 1.3.1.12 の具体的な正規化微分の計算。 -/
lemma moore_d_arrow (W : SimplicialObject (ModuleCat.{u} R)) (n : ℕ) :
    ((normalizedMooreComplex (ModuleCat.{u} R)).obj W).d (n + 1) n ≫
      (NormalizedMooreComplex.objX W n).arrow =
        (NormalizedMooreComplex.objX W (n + 1)).arrow ≫ W.δ 0 := by
  rw [normalizedMooreComplex_objD]
  cases n with
  | zero => simp [NormalizedMooreComplex.objD, Category.assoc]
  | succ n =>
    dsimp only [NormalizedMooreComplex.objD]
    rw [Subobject.factorThru_arrow]

/-- 概要：標準 Hom の具体的正規化への同型は元の単体への包含と可換である。
方針：各項の同型の定義を次数で場合分けして展開する。
規約：零次数の全体部分加群も含める。
使われ方：HA 1.3.1.12 の抽象的 Moore 複体から成分への評価。 -/
lemma standardMooreTermIso_hom_subtype (x y : D) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y n).hom ≫
      ModuleCat.ofHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizedSubmodule R x y n).subtype =
        (NormalizedMooreComplex.objX (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) n).arrow := by
  cases n <;> rfl

/-- 概要：零番目の面の全頂点の像は元の単体の零番目の頂点を除いた集合である。
方針：succAbove 0 の像を零以外の Fin の元と同定する。
規約：退化でない余面写像を使う。
使われ方：HA 1.3.1.12 の正規化微分の成分の計算。 -/
lemma faceZero_image_univ (n : ℕ) :
    (Finset.univ : Finset (Fin (n + 1))).image
      (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom = Finset.univ.erase 0 := by
  ext j
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
  change (∃ a, (0 : Fin (n + 2)).succAbove a = j) ↔ j ≠ 0
  simp only [Fin.succAbove_zero]
  exact ⟨fun ⟨a, ha⟩ ↦ ha ▸ Fin.succ_ne_zero a, Fin.exists_succ_eq_of_ne_zero⟩

/-- 概要：標準単体の零番目の面の最上位成分は元の零番目の面の成分である。
方針：引き戻しの成分計算と全体集合の像の同定を使う。
規約：次数を証明引数で保持し、次数の移送を挿入しない。
使われ方：HA 1.3.1.12 の Moore 微分の最上位評価。 -/
lemma standardFaceZero_top {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1)) (k : ℤ)
    (hk : k = 1 - ((Finset.univ : Finset (Fin (n + 1))).card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom f).val.component
      Finset.univ k Finset.univ_nonempty hk =
        f.val.component (Finset.univ.erase 0) k
          (by apply Finset.card_pos.mp; simp) (by simpa using hk) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback_val, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _
    (0 : Fin (n + 2)).succAboveOrderEmb.injective.injOn]
  have hm (I J : Finset (Fin (n + 2))) (he : I = J)
      (hI : I.Nonempty) (hJ : J.Nonempty)
      (hki : k = 1 - (I.card : ℤ)) (hkj : k = 1 - (J.card : ℤ)) :
      f.val.component I k hI hki = f.val.component J k hJ hkj := by subst J; rfl
  exact hm _ _ (faceZero_image_univ n) _ _ _ _

/-- 概要：正規化された標準単体の最上位成分の微分は零番目の面の成分である。
方針：標準方程式による微分の計算で、終次数を別変数として指定する。
規約：終次数は始次数 +1 と仮定し、同じ次数の項で比較する。
使われ方：HA 1.3.1.12 の正規化複体の射の可換性。 -/
lemma normalized_top_d {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R x y (n + 1))
    (hf : f ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardNormalizedSubmodule R x y (n + 1)) (p q : ℤ)
    (hp : p = 1 - ((Finset.univ : Finset (Fin (n + 2))).card : ℤ)) (hpq : q = p + 1) :
    (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d p q (f.val.component Finset.univ p Finset.univ_nonempty hp) =
      f.val.component (Finset.univ.erase 0) q
        (by apply Finset.card_pos.mp; simp) (by simp at hp ⊢; omega) := by
  subst hpq
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.normalized_top_differential f hf p hp

/-- 概要：Moore 微分を具体的正規化へ移すと標準単体の零番目の面となる。
方針：抽象的包含と具体的包含の可換性を微分と包含の等式へ代入する。
規約：台の標準単体として等しいことを述べる。
使われ方：HA 1.3.1.12 の各項の同型と微分の両立。 -/
lemma standardMooreTermIso_d_val (x y : D) (n : ℕ)
    (s : ((normalizedMooreComplex (ModuleCat.{u} R)).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).X (n + 1)) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y n).hom
      (((normalizedMooreComplex (ModuleCat.{u} R)).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).d (n + 1) n s)).val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardPullback (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y (n + 1)).hom s).val := by
  have h := moore_d_arrow (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y) n
  rw [← standardMooreTermIso_hom_subtype x y n,
    ← standardMooreTermIso_hom_subtype x y (n + 1)] at h
  exact congrArg (fun f ↦ f s) h

/-- 概要：正次数間の Moore 微分は最上位評価で元の Hom の微分に一致する。
方針：Moore 微分を零番目の面に移し、その最上位成分を標準方程式で計算する。
規約：cochain の始次数と終次数はそれぞれ −(n+2)、−(n+1)。
使われ方：HA 1.3.1.12 の正規化と切断 Hom の複体同型の正次数部分。 -/
lemma standardMoorePositiveIso_d (x y : D) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMoorePositiveIso (R := R) x y (n + 1)).hom ≫
      (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) =
        ((normalizedMooreComplex (ModuleCat.{u} R)).obj
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).d (n + 2) (n + 1) ≫
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMoorePositiveIso (R := R) x y n).hom := by
  apply ConcreteCategory.hom_ext
  intro s
  change (_root_.SerrePositivity.DifferentialGraded.homObject R D x y).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ))
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y (n + 2)).hom s).val.val.component
      Finset.univ (-(n + 2 : ℤ)) Finset.univ_nonempty (by simp)) =
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y (n + 1)).hom
      (((normalizedMooreComplex (ModuleCat.{u} R)).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardModule (R := R) x y)).d
        (n + 2) (n + 1) s)).val.val.component Finset.univ (-(n + 1 : ℤ))
          Finset.univ_nonempty (by simp))
  rw [standardMooreTermIso_d_val]
  rw [standardFaceZero_top]
  exact normalized_top_d _ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardMooreTermIso (R := R) x y (n + 2)).hom s).property
    _ _ (by simp; omega) (by omega)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

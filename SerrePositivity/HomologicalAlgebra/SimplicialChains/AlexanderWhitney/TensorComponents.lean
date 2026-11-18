module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Finite

/-!
# 自然数鎖複体のテンソルの有限成分

概要：各全次数の有限直和を有限直積として使うための射影と lift を構成する。
方針：既存のテンソル複体の余積を標準の有限双積と同一視する。
規約：次数は自然数、微分は −1、第二因子の符号は (−1)^p。
使われ方：AW 成分を鎖写像に束ね、等式を全ての二次数で検査する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.AlexanderWhitney

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

local instance _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.instFiniteSubtypeProdNatEqHAddFstSnd_serrePositivity (n : ℕ) : Finite {i : ℕ × ℕ // i.1 + i.2 = n} :=
  inferInstanceAs (Finite ((fun i : ℕ × ℕ => i.1 + i.2) ⁻¹' {n}))

/-- 概要：全次数 n のテンソル因子の有限族（Berger–Fresse §1.1.4 の有限成分）。
方針：二つの鎖次数の和が n となる添字を取る。
規約：自然数次数なので族は有限。
使われ方：AW 対角を有限双積へ束ねる。 -/
abbrev tensorFactors (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ)
    (i : {i : ℕ × ℕ // i.1 + i.2 = n}) : ModuleCat A := K.X i.val.1 ⊗ L.X i.val.2

/-- 概要：テンソルの各全次数と有限双積との標準同型（Berger–Fresse §1.1.4 の有限成分）。
方針：既存の余積と有限双積の標準同型を使う。
規約：既存のテンソル複体の次数対象を保つ。
使われ方：射影と lift の定義。 -/
def tensorBiproductIso (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    (⨁ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n) ≅ (HomologicalComplex.tensorObj K L).X n :=
  biproduct.isoCoproduct _

/-- 概要：テンソル複体の (p,q) 成分への射影（Berger–Fresse §1.1.4 の有限成分）。
方針：有限双積の射影を標準同型で移す。
規約：p+q=n の指定を引数に含む。
使われ方：AW とテンソル微分を成分で比較する。 -/
def tensorProjection (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (n p q : ℕ) (h : p + q = n) :
    (HomologicalComplex.tensorObj K L).X n ⟶ K.X p ⊗ L.X q :=
  (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorBiproductIso K L n).inv ≫ biproduct.π (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n) ⟨(p, q), h⟩

/-- 概要：同じ二次数の包含と射影の合成は恒等射（Berger–Fresse §1.1.4 の有限成分）。
方針：標準同型を展開して双積の包含と射影の公式を使う。
規約：全次数と二次数の指定を共通に取る。
使われ方：テンソル微分と自然性の射影計算。 -/
@[reassoc (attr := simp)]
lemma tensorInclusion_projection (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (n p q : ℕ) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n p q h = 𝟙 _ := by
  change Sigma.ι (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n) ⟨(p, q), h⟩ ≫
    (biproduct.isoCoproduct (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n)).inv ≫
      biproduct.π (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n) ⟨(p, q), h⟩ = _
  simp [biproduct.isoCoproduct_inv]

/-- 概要：異なる二次数の包含と射影の合成は零（Berger–Fresse §1.1.4 の有限成分）。
方針：添字の不一致を双積の射影公式へ渡す。
規約：二つの二次数の全次数は同じである。
使われ方：テンソル微分で残る成分を特定する。 -/
@[reassoc (attr := simp)]
lemma tensorInclusion_projection_ne (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (n p q r s : ℕ) (h : p + q = n) (h' : r + s = n) (hne : (p, q) ≠ (r, s)) :
    ιTensorObj K L p q n h ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n r s h' = 0 := by
  have hi : (⟨(p, q), h⟩ : {i : ℕ × ℕ // i.1 + i.2 = n}) ≠ ⟨(r, s), h'⟩ :=
    fun e => hne (congrArg Subtype.val e)
  change Sigma.ι (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n) ⟨(p, q), h⟩ ≫
    (biproduct.isoCoproduct (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n)).inv ≫
      biproduct.π (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n) ⟨(r, s), h'⟩ = _
  simp [biproduct.isoCoproduct_inv, hi]

/-- 概要：有限個の二次数への射を全次数への射へ束ねる（Berger–Fresse §1.1.4 の有限成分）。
方針：有限双積の lift を標準同型で移す。
規約：全ての p+q=n の成分を入力とする。
使われ方：AW 対角の次数ごとの射を構成する。 -/
def tensorLift (K L : ChainComplex (ModuleCat.{u} A) ℕ) {M : ModuleCat.{u} A} (n : ℕ)
    (f : ∀ p q, (p + q = n) → (M ⟶ (K.X p ⊗ L.X q))) : M ⟶ (HomologicalComplex.tensorObj K L).X n :=
  biproduct.lift (f := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n) (fun i => f i.val.1 i.val.2 i.property) ≫
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorBiproductIso K L n).hom

/-- 概要：束ねた射の射影は指定した成分（Berger–Fresse §1.1.4 の有限成分）。
方針：標準同型とその逆を消去して双積の lift の公式を使う。
規約：全ての次数分割の入力に適用する。
使われ方：AW 対角の元の成分を復元する。 -/
@[reassoc (attr := simp)]
lemma tensorLift_projection (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    {M : ModuleCat.{u} A} (n : ℕ) (f : ∀ p q, (p + q = n) → (M ⟶ (K.X p ⊗ L.X q)))
    (p q : ℕ) (h : p + q = n) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorLift K L n f ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n p q h = f p q h := by
  simp [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorLift, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection]

/-- 概要：全次数への射は全二次数への射影で決まる（Berger–Fresse §1.1.4 の有限成分）。
方針：有限双積の外延性を使う。
規約：始域は任意の係数加群。
使われ方：AW の鎖写像条件と自然性を検査する。 -/
lemma tensorProjection_hom_ext (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    {M : ModuleCat.{u} A} {n : ℕ} {f g : M ⟶ (HomologicalComplex.tensorObj K L).X n}
    (h : ∀ p q (hpq : p + q = n),
      f ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n p q hpq = g ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n p q hpq) : f = g := by
  apply (cancel_mono (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorBiproductIso K L n).inv).1
  apply biproduct.hom_ext
  intro i
  simpa only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection, Category.assoc] using h i.val.1 i.val.2 i.property

/-- 概要：テンソル微分の第一因子の射影公式（Berger–Fresse §1.1.4 の有限成分）。
方針：各直和包含で検査し次数零と正次数に分ける。
規約：第一因子の微分には符号を付けない。
使われ方：テンソル微分全体の射影公式。 -/
lemma tensorD₁_projection (K L : ChainComplex (ModuleCat.{u} A) ℕ) (p q : ℕ) :
    mapBifunctor.D₁ K L (curriedTensor (ModuleCat A)) (.down ℕ) (p + q + 1) (p + q) ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L (p + q) p q rfl =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L (p + q + 1) (p + 1) q (by omega) ≫
        (K.d (p + 1) p ▷ L.X q) := by
  apply mapBifunctor.hom_ext
  intro r s hrs
  rw [mapBifunctor.ι_D₁_assoc]
  cases r with
  | zero =>
    rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp)]
    rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne_assoc _ _ _ _ _ _ _ hrs _ (by
      intro e
      have he := congrArg Prod.fst e
      omega)]
    simp
  | succ r =>
    rw [mapBifunctor.d₁_eq K L (curriedTensor (ModuleCat A)) (.down ℕ)
      (show (ComplexShape.down ℕ).Rel (r + 1) r from rfl) s (p + q) (by dsimp at hrs ⊢; omega)]
    rw [show ComplexShape.ε₁ (.down ℕ) (.down ℕ) (.down ℕ) (r + 1, s) = 1 from rfl]
    simp only [one_smul, Category.assoc]
    by_cases hr : r = p
    · subst r
      have hs : s = q := by dsimp at hrs; omega
      subst s
      simp
    · rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne _ _ _ _ _ _ _ _ (by omega) (by
        intro e
        exact hr (congrArg Prod.fst e)),
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne_assoc _ _ _ _ _ _ _ hrs _ (by
      intro e
      have he := congrArg Prod.fst e
      omega)]
      simp

/-- 概要：テンソル微分の第二因子の射影公式（Berger–Fresse §1.1.4 の有限成分）。
方針：各直和包含で検査し単位整数の符号を整数へ移す。
規約：Koszul 符号は第一因子の次数による。
使われ方：component_d と同じ符号の微分公式を得る。 -/
lemma tensorD₂_projection (K L : ChainComplex (ModuleCat.{u} A) ℕ) (p q : ℕ) :
    mapBifunctor.D₂ K L (curriedTensor (ModuleCat A)) (.down ℕ) (p + q + 1) (p + q) ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L (p + q) p q rfl =
      (-1 : ℤ) ^ p • (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L (p + q + 1) p (q + 1) (by omega) ≫
        (K.X p ◁ L.d (q + 1) q)) := by
  apply mapBifunctor.hom_ext
  intro r s hrs
  rw [mapBifunctor.ι_D₂_assoc]
  cases s with
  | zero =>
    rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp)]
    simp only [Preadditive.comp_zsmul, ← Category.assoc]
    rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne _ _ _ _ _ _ _ hrs _ (by
      intro e
      have he := congrArg Prod.snd e
      omega)]
    simp
  | succ s =>
    rw [mapBifunctor.d₂_eq K L (curriedTensor (ModuleCat A)) (.down ℕ) r
      (show (ComplexShape.down ℕ).Rel (s + 1) s from rfl) (p + q) (by dsimp at hrs ⊢; omega)]
    have he : ComplexShape.ε₂ (.down ℕ) (.down ℕ) (.down ℕ) (r, s + 1) =
        (-1 : ℤˣ) ^ r := rfl
    rw [he]
    simp only [Units.smul_def, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    by_cases hr : r = p
    · subst r
      have hs : s = q := by dsimp at hrs; omega
      subst s
      simp
    · rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne _ _ _ _ _ _ _ _ (by omega) (by
        intro e
        exact hr (congrArg Prod.fst e))]
      rw [← Category.assoc, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne _ _ _ _ _ _ _ hrs _ (by
      intro e
      have he := congrArg Prod.fst e
      omega)]
      simp

/-- 概要：テンソル微分の射影公式（Berger–Fresse §1.1.4 の有限成分）。
方針：第一因子と第二因子の微分項を加える。
規約：後半の符号は (−1)^p。
使われ方：AW 成分の微分公式から鎖写像を構成する。 -/
lemma tensor_d_projection (K L : ChainComplex (ModuleCat.{u} A) ℕ) (p q : ℕ) :
    (HomologicalComplex.tensorObj K L).d (p + q + 1) (p + q) ≫
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L (p + q) p q rfl =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L (p + q + 1) (p + 1) q (by omega) ≫ (K.d (p + 1) p ▷ L.X q) +
      (-1 : ℤ) ^ p • (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L (p + q + 1) p (q + 1) (by omega) ≫
        (K.X p ◁ L.d (q + 1) q)) := by
  rw [mapBifunctor.d_eq, Preadditive.add_comp, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorD₁_projection, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorD₂_projection]

/-- 概要：テンソル鎖写像の射影公式（Berger–Fresse §1.1.4 の有限成分）。
方針：各直和包含で検査し一致する二次数だけを残す。
規約：二つの鎖写像は次数を保つ。
使われ方：AW 鎖写像の自然性と余結合性。 -/
@[reassoc (attr := simp)]
lemma tensorHom_projection {K L K' L' : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') (n p q : ℕ) (h : p + q = n) :
    (HomologicalComplex.tensorHom f g).f n ≫ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K' L' n p q h =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n p q h ≫ (f.f p ⊗ₘ g.f q) := by
  apply mapBifunctor.hom_ext
  intro r s hrs
  rw [ι_mapBifunctorMap_assoc]
  by_cases he : (r, s) = (p, q)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    simp [MonoidalCategory.tensorHom_def]
  · rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne _ _ _ _ _ _ _ hrs h he,
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorInclusion_projection_ne_assoc _ _ _ _ _ _ _ hrs h he]
    simp

local instance _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.instFintypeSubtypeProdNatEqHAddFstSnd_serrePositivity (n : ℕ) : Fintype {i : ℕ × ℕ // i.1 + i.2 = n} := Fintype.ofFinite _

/-- 概要：lift の次数分割による有限和公式（Berger–Fresse §1.1.4 の有限成分）。
方針：双積の lift の有限和表示を標準同型で移す。
規約：添字は p+q=n を満たす自然数の対。
使われ方：AW 対角を有限和で計算する。 -/
lemma tensorLift_eq_sum (K L : ChainComplex (ModuleCat.{u} A) ℕ) {N : ModuleCat.{u} A}
    (n : ℕ) (f : ∀ p q, (p + q = n) → (N ⟶ (K.X p ⊗ L.X q))) :
    _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorLift K L n f = ∑ i : {i : ℕ × ℕ // i.1 + i.2 = n},
      f i.val.1 i.val.2 i.property ≫ ιTensorObj K L i.val.1 i.val.2 n i.property := by
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorLift, biproduct.lift_eq, Preadditive.sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  simp only [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorBiproductIso, biproduct.isoCoproduct_hom, Category.assoc,
    biproduct.ι_desc]
  rfl

/-- 概要：全次数の恒等射の射影と包含による有限和表示（Berger–Fresse §1.1.4 の有限成分）。
方針：有限双積の恒等射の分解を標準同型で移す。
規約：同じ双積の射影と包含を用いる。
使われ方：テンソル因子を追加した後の射影の外延性。 -/
lemma tensorProjection_total (K L : ChainComplex (ModuleCat.{u} A) ℕ) (n : ℕ) :
    ∑ i : {i : ℕ × ℕ // i.1 + i.2 = n},
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n i.val.1 i.val.2 i.property ≫
        ιTensorObj K L i.val.1 i.val.2 n i.property = 𝟙 _ := by
  have hi (i : {i : ℕ × ℕ // i.1 + i.2 = n}) :
      ιTensorObj K L i.val.1 i.val.2 n i.property =
        biproduct.ι (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n) i ≫ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorBiproductIso K L n).hom := by
    change Sigma.ι (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n) i =
      biproduct.ι (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorFactors K L n) i ≫ (biproduct.isoCoproduct _).hom
    simp [biproduct.isoCoproduct_hom]
  simp only [hi, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection, Category.assoc, ← Preadditive.comp_sum]
  simp only [← Category.assoc, ← Preadditive.sum_comp, biproduct.total]
  simp

/-- 概要：固定因子をテンソルした後の射影の外延性（Berger–Fresse §1.1.4 の有限成分）。
方針：恒等射の有限和表示をテンソルし加法性を使う。
規約：固定因子は任意の係数加群。
使われ方：三重テンソルへの射の等式を三つの次数で検査する。 -/
lemma whiskerLeft_tensorProjection_hom_ext (T : ModuleCat.{u} A)
    (K L : ChainComplex (ModuleCat.{u} A) ℕ) {N : ModuleCat.{u} A} {n : ℕ}
    {f g : N ⟶ T ⊗ (HomologicalComplex.tensorObj K L).X n}
    (h : ∀ p q (hpq : p + q = n),
      f ≫ (T ◁ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n p q hpq) =
        g ≫ (T ◁ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n p q hpq)) : f = g := by
  have ht := congrArg (fun φ => T ◁ φ) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection_total K L n)
  simp only [whiskerLeft_sum, MonoidalCategory.whiskerLeft_comp,
    MonoidalCategory.whiskerLeft_id] at ht
  calc
    f = f ≫ ∑ i : {i : ℕ × ℕ // i.1 + i.2 = n},
        (T ◁ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n i.val.1 i.val.2 i.property) ≫
          (T ◁ ιTensorObj K L i.val.1 i.val.2 n i.property) := by rw [ht, Category.comp_id]
    _ = g ≫ ∑ i : {i : ℕ × ℕ // i.1 + i.2 = n},
        (T ◁ _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.tensorProjection K L n i.val.1 i.val.2 i.property) ≫
          (T ◁ ιTensorObj K L i.val.1 i.val.2 n i.property) := by
      simp only [Preadditive.comp_sum, ← Category.assoc]
      apply Finset.sum_congr rfl
      intro i _
      rw [h i.val.1 i.val.2 i.property]
    _ = g := by rw [ht, Category.comp_id]

end SerrePositivity.SimplicialChains.AlexanderWhitney

module
public import SerrePositivity.DifferentialGraded.Complexes.AssociatorCochainNaturality
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition
public import SerrePositivity.DifferentialGraded.Complexes.TensorClosedZero

/-! # 先頭二因子の合成と結合的作用に対する任意次数cochainの自然性

## 概要
先頭二因子の合成と結合的作用に対する任意次数cochainの自然性。

## 方針
既存の全dg自然なHom・作用・chain mapと局所化の計算を再利用する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。dg加群の導来作用・準同値比較の基盤。任意可換環上のMorita・K理論のモデル比較に再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

lemma tensorJoin_action_cochain (U V W P Q R T : Complex A) (p : ℤ)
    (f : Cochain P Q p) (c : U ⊗ V ⟶ W) (r : W ⊗ Q ⟶ T)
    (s : V ⊗ Q ⟶ R) (t : U ⊗ R ⟶ T)
    (hc : (α_ U V Q).inv ≫ (c ▷ Q) ≫ r = (U ◁ s) ≫ t) :
    (Cochain.ofHom ((α_ U V P).inv ≫ c ▷ P)).comp
      (((tensorLeftHom W P Q).f p f).comp (Cochain.ofHom r) (add_zero p)) (zero_add p) =
    ((tensorLeftHom U (V ⊗ P) R).f p
      (((tensorLeftHom V P Q).f p f).comp (Cochain.ofHom s) (add_zero p))).comp
      (Cochain.ofHom t) (add_zero p) := by
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, tensorJoin_cochain_naturality,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    Category.assoc, hc]

end SerrePositivity.DifferentialGraded

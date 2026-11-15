module

public import SerrePositivity.InfinityCategories.HA.Monads.AugmentedOrdinalTensorMaps
public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalMixedAdjoints
public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalActionComparison

/-!
概要：水平作用の全射を順序和の有限単調射の表示へ移す。
方針：全関手の等式から射の異種等式を取り、構成済みの有限随伴の型の輸送も用意する。
規約：対象の個数の等式を明示し、異なる有限区間を同じ型だと仮定しない。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の全水平結合則。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory MonoidalCategory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：増大単体圏への関手の等式は有限単調射の表示を保つ。
方針：同じ関手へ戻して比較する。規約：全ての添字圏の射。
使われ方：Riehl–Verity Remark 3.3.8 の水平作用の自然性の移送。 -/
lemma augmentedOrderHom_functor_map_heq {I : Type u} [Category.{v} I]
    {F G : I ⥤ AugmentedSimplexCategory} (h : F = G) {X Y : I} (f : X ⟶ Y) :
    HEq (augmentedOrderHom (F.map f)) (augmentedOrderHom (G.map f)) := by
  cases h
  rfl

/-- 概要：有限区間の型の輸送で区間表示も移る。
方針：個数と射を同じに戻す。規約：元の有限順序集合は空も許す。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の係数移送。 -/
lemma ordinalIntervalMap_heq {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    {f : Fin a →o Fin b} {g : Fin c →o Fin d} (h : HEq f g) :
    HEq (ordinalIntervalMap f) (ordinalIntervalMap g) := by
  subst c
  subst d
  have hfg : f = g := eq_of_heq h
  subst g
  rfl

/-- 概要：有限区間の型の輸送で構成済みの右随伴も移る。
方針：個数と射を戻し、端点条件の証明非依存性を使う。
規約：実右随伴のまま。使われ方：Riehl–Verity Remark 3.3.8 の混合合成の係数移送。 -/
lemma ordinalRightAdjoint_heq {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    {f : Fin (a + 1) →o Fin (b + 1)} {g : Fin (c + 1) →o Fin (d + 1)}
    (hf : f 0 = 0) (hg : g 0 = 0) (h : HEq f g) :
    HEq (ordinalRightAdjoint f hf) (ordinalRightAdjoint g hg) := by
  subst c
  subst d
  have hfg : f = g := eq_of_heq h
  subst g
  rfl

/-- 概要：同じ輸送で構成済みの左随伴も移る。
方針：同じ射の最大元条件の証明非依存性を使う。
規約：元の実左随伴を保持する。使われ方：Riehl–Verity Remark 3.3.8 の係数移送。 -/
lemma ordinalLeftAdjoint_heq {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    {f : Fin (a + 1) →o Fin (b + 1)} {g : Fin (c + 1) →o Fin (d + 1)}
    (hf : f (Fin.last a) = Fin.last b) (hg : g (Fin.last c) = Fin.last d)
    (h : HEq f g) : HEq (ordinalLeftAdjoint f hf) (ordinalLeftAdjoint g hg) := by
  subst c
  subst d
  have hfg : f = g := eq_of_heq h
  subst g
  rfl

/-- 概要：区間の射の回収も同じ個数と射の輸送に適合する。
方針：構成済みの回収を同じ端点条件の下で比較する。
規約：両端点の条件を残す。使われ方：Riehl–Verity Remark 3.3.8 の逆区間表示の照合。 -/
lemma ordinalRecoverMap_heq {a b c d : ℕ} (hac : a = c) (hbd : b = d)
    {f : Fin (a + 1) →o Fin (b + 1)} {g : Fin (c + 1) →o Fin (d + 1)}
    (hf₀ : f 0 = 0) (hf₁ : f (Fin.last a) = Fin.last b)
    (hg₀ : g 0 = 0) (hg₁ : g (Fin.last c) = Fin.last d) (h : HEq f g) :
    HEq (ordinalRecoverMap f hf₀ hf₁) (ordinalRecoverMap g hg₀ hg₁) := by
  subst c
  subst d
  have hfg : f = g := eq_of_heq h
  subst g
  rfl

/-- 概要：最大元保存の左作用の全射は元の有限単調射の順序和。
方針：忘却後の全関手の等式と、非空の右因子の順序和の照合を使う。
規約：空から非空への射も含む。使われ方：HA Proposition 4.7.3.3 の全結合則。 -/
lemma topOrdinalAction_map_heq {A B : AugmentedSimplexCategory} {X Y : TopSimplexCategory}
    (f : A ⟶ B) (g : X ⟶ Y) :
    HEq (topOrdinalAction.map (X := (A, X)) (Y := (B, Y)) (f, g)).hom.toOrderHom
      (ordinalAppend (augmentedOrderHom f) g.hom.toOrderHom) := by
  have h := augmentedOrderHom_functor_map_heq topOrdinalAction_forget
    (X := (A, X)) (Y := (B, Y)) (f, g)
  change HEq (topOrdinalAction.map (X := (A, X)) (Y := (B, Y)) (f, g)).hom.toOrderHom
    (augmentedOrderHom (f ⊗ₘ WithInitial.incl.map g.hom)) at h
  exact h.trans (augmentedOrderHom_tensor_nonempty_right f g.hom)

/-- 概要：最小元保存の右作用の全射は元の有限単調射の順序和。
方針：既存の全自然性を忘却後に使い、非空の左因子の射を照合する。
規約：右の空の因子も許す。使われ方：HA Proposition 4.7.3.3 の全結合則。 -/
lemma bottomOrdinalAction_map_heq {A B : AugmentedSimplexCategory}
    {X Y : BottomSimplexCategory} (f : X ⟶ Y) (g : A ⟶ B) :
    HEq (bottomOrdinalAction.map (X := (X, A)) (Y := (Y, B)) (f, g)).hom.toOrderHom
      (ordinalAppend f.hom.toOrderHom (augmentedOrderHom g)) := by
  have h := augmentedOrderHom_functor_map_heq bottomOrdinalAction_forget
    (X := (X, A)) (Y := (Y, B)) (f, g)
  change HEq (bottomOrdinalAction.map (X := (X, A)) (Y := (Y, B)) (f, g)).hom.toOrderHom
    (augmentedOrderHom (WithInitial.incl.map f.hom ⊗ₘ g)) at h
  exact h.trans (augmentedOrderHom_tensor_nonempty_left f.hom g)

end SerrePositivity.InfinityCategories.HA.Monads

module

public import SerrePositivity.EInfinity.SimplicialLocalization.ResolutionGenerators

/-!
# 自由解像の全次数の標準対象と射の表示

概要：Dwyer–Kan の反復自由圏の元の対象と射を同じ固定 Hom へ送る。
方針：元の対象を反復して自由圏へ送り、augmentation の対象単射性で表示を同定する。
規約：元の自由解像・局所化・固定対象表示を保持する。
使われ方：一次の辺の二面による生成射の恒等・合成則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory Opposite
open SerrePositivity.HomotopyFunctionComplex.ComonadResolutionOperators
open scoped Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

/-- 概要：反復自由相対圏の元の対象の標準表示（Dwyer–Kan）。
方針：元の対象へ一文字の列の対象写像を反復する。
規約：自由圏の対象は元の対象を保持する。
使われ方：全次数の固定 Hom への元の射の移送。 -/
def freeResolutionGeneratorObject : (n : ℕ) → C.category → (power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n).category
  | 0, X => X
  | n + 1, X => (Paths.of _).obj (freeResolutionGeneratorObject n X)

/-- 概要：標準生成対象の augmentation は元の対象（Dwyer–Kan）。
方針：列の合成の対象写像が恒等であることを反復する。
規約：元の comonad の同じ augmentation。
使われ方：局所化した標準対象と固定表示の同定。 -/
lemma freeResolutionGeneratorObject_augmentation (n : ℕ) (X : C.category) :
    (augmentation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n).functor.obj (freeResolutionGeneratorObject C n X) =
      X := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- 概要：各次数の固定対象表示は標準生成対象の局所化像（Dwyer–Kan）。
方針：augmentation の対象単射性と局所化の厳密な因子化を使う。
規約：同じ対象の表示を全次数で保持する。
使われ方：元の自由射を固定 Hom の単体へ移す。 -/
lemma localizedFreeResolutionObject_generator (n : ℕ) (X : C.category) :
    localizedFreeResolutionObject C (op ⦋n⦌) X =
      (power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1)).weakEquivalences.Q.obj
        (freeResolutionGeneratorObject C (n + 1) X) := by
  apply (localizedFreeResolutionObjectEquiv C (op ⦋n⦌)).injective
  change ((localizedFreeResolutionAugmentation C).app (op ⦋n⦌)).toFunctor.obj
      (localizedFreeResolutionObject C (op ⦋n⦌) X) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap (augmentation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1))).obj
      ((power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1)).weakEquivalences.Q.obj
        (freeResolutionGeneratorObject C (n + 1) X))
  rw [localizedFreeResolutionAugmentation_object]
  have h := Functor.congr_obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac (augmentation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1)))
    (freeResolutionGeneratorObject C (n + 1) X)
  simpa only [Functor.comp_obj, freeResolutionGeneratorObject_augmentation] using h.symm

/-- 概要：反復自由圏の元の射を同じ固定 Hom の単体へ送る（Dwyer–Kan）。
方針：同じ局所化像を標準対象と固定表示の同じ等式で移す。
規約：全次数で元の射を保持する。
使われ方：一次の辺の明示的な構成。 -/
def localizationResolutionHom (n : ℕ) {X Y : C.category}
    (f : freeResolutionGeneratorObject C (n + 1) X ⟶
      freeResolutionGeneratorObject C (n + 1) Y) : (localizationHom C X Y) _⦋n⦌ :=
  eqToHom (localizedFreeResolutionObject_generator C n X) ≫
    (power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C (n + 1)).weakEquivalences.Q.map f ≫
      eqToHom (localizedFreeResolutionObject_generator C n Y).symm

/-- 概要：標準射の表示は元の恒等射を保つ（Dwyer–Kan）。
方針：元の局所化関手の恒等則と対象移送の相殺を使う。
規約：全次数の同じ恒等射。
使われ方：生成射の類の恒等則。 -/
lemma localizationResolutionHom_id (n : ℕ) (X : C.category) :
    localizationResolutionHom C n (𝟙 (freeResolutionGeneratorObject C (n + 1) X)) =
      𝟙 (localizedFreeResolutionObject C (op ⦋n⦌) X) := by
  simp [localizationResolutionHom]

/-- 概要：標準射の表示は元の自由圏の合成を保つ（Dwyer–Kan）。
方針：元の局所化関手の合成則と中間対象の移送の相殺を使う。
規約：全次数の同じ合成順序。
使われ方：生成射の類の合成則。 -/
lemma localizationResolutionHom_comp (n : ℕ) {X Y Z : C.category}
    (f : freeResolutionGeneratorObject C (n + 1) X ⟶
      freeResolutionGeneratorObject C (n + 1) Y)
    (g : freeResolutionGeneratorObject C (n + 1) Y ⟶
      freeResolutionGeneratorObject C (n + 1) Z) :
    localizationResolutionHom C n (f ≫ g) =
      localizationResolutionHom C n f ≫ localizationResolutionHom C n g := by
  simp [localizationResolutionHom, Category.assoc]

/-- 概要：零次の一文字の射の表示は元の同じ零単体（Dwyer–Kan）。
方針：二つの対象等式の証明は命題の証明なので一致する。
規約：元の一文字の列を保持する。
使われ方：一次の面の計算を既存の生成射へ接続する。 -/
lemma localizationResolutionHom_zero_arrow {X Y : C.category} (f : X ⟶ Y) :
    localizationResolutionHom C 0 ((Paths.of C.category).map f) =
      localizationArrowZero C f := rfl

end SerrePositivity.EInfinity.SimplicialLocalization

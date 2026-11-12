module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom

/-!
# 対象表示を保つ図式の係数射の固定 Hom への作用

概要：Dwyer–Kan の固定対象の Hom に図式の係数自然変換を送る。
方針：同じ対象表示の等式で各成分の元の Hom 作用を移す。
規約：係数自然性と対象表示の保存を明示的に使う。
使われ方：単体的局所化の Hom の係数自然性。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section

universe u v w w'

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality

open CategoryTheory

variable {I : Type v} [Category I] (D E : I ⥤ Cat.{u, u})
  {O : Type w} {P : Type w'} (p : (i : I) → O → D.obj i)
  (q : (i : I) → P → E.obj i)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).toFunctor.obj (p i X) = p j X)
  (hq : ∀ {i j : I} (θ : i ⟶ j) (X : P), (E.map θ).toFunctor.obj (q i X) = q j X)
  (η : D ⟶ E) (φ : O → P)
  (hη : ∀ (i : I) (X : O), (η.app i).toFunctor.obj (p i X) = q i (φ X))

/-- 概要：図式の係数射を固定対象の Hom へ送る（Dwyer–Kan）。
方針：各成分の元の関手の作用を対象表示の等式で移す。
規約：対象の係数写像 φ を保持する。
使われ方：固定 Hom の係数自然変換の成分。 -/
def coefficientMap (i : I) {X Y : O} (f : p i X ⟶ p i Y) : q i (φ X) ⟶ q i (φ Y) :=
  eqToHom (hη i X).symm ≫ (η.app i).toFunctor.map f ≫ eqToHom (hη i Y)

/-- 概要：固定 Hom の係数射は全作用素に自然（Dwyer–Kan）。
方針：元の係数自然性の関手等式を Hom に評価して対象移送を相殺する。
規約：全ての作用素と固定した元の両対象を含む。
使われ方：係数射を単体写像に束ねる。 -/
lemma coefficientMap_naturality {i j : I} (θ : i ⟶ j) {X Y : O} (f : p i X ⟶ p i Y) :
    coefficientMap D E p q η φ hη j (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map D p hp θ f) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map E q hq θ (coefficientMap D E p q η φ hη i f) := by
  have h : (D.map θ).toFunctor ⋙ (η.app j).toFunctor =
      (η.app i).toFunctor ⋙ (E.map θ).toFunctor :=
    congrArg Cat.Hom.toFunctor (η.naturality θ)
  have hf := Functor.congr_hom h f
  simp only [Functor.comp_map] at hf
  unfold coefficientMap _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.map
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [hf]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans]

/-- 概要：固定 Hom の係数射は元の恒等射を保つ（Dwyer–Kan）。
方針：元の成分関手の恒等則と対象移送の相殺を使う。
規約：同じ次数の元の恒等射。
使われ方：係数豊穣関手の単位則。 -/
lemma coefficientMap_identity (i : I) (X : O) :
    coefficientMap D E p q η φ hη i (𝟙 (p i X)) = 𝟙 (q i (φ X)) := by
  simp [coefficientMap]

/-- 概要：固定 Hom の係数射は元の合成を保つ（Dwyer–Kan）。
方針：元の成分関手の合成則と中間対象の移送の相殺を使う。
規約：各次数の実際の圏の合成。
使われ方：係数豊穣関手の合成則。 -/
lemma coefficientMap_composition (i : I) {X Y Z : O}
    (f : p i X ⟶ p i Y) (g : p i Y ⟶ p i Z) :
    coefficientMap D E p q η φ hη i (f ≫ g) =
      coefficientMap D E p q η φ hη i f ≫ coefficientMap D E p q η φ hη i g := by
  simp [coefficientMap, Category.assoc]

/-- 概要：図式の係数射を固定 Hom 関手の自然変換に束ねる（Dwyer–Kan）。
方針：同じ成分写像と全作用素に対する自然性を使う。
規約：元の図式と対象表示を保持する。
使われ方：単体的局所化の Hom の間の単体写像。 -/
def coefficientNatTrans (X Y : O) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor D p hp X Y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom.functor E q hq (φ X) (φ Y) where
  app i := ↾(coefficientMap D E p q η φ hη i)
  naturality i j θ := by
    apply ConcreteCategory.hom_ext
    intro f
    exact coefficientMap_naturality D E p q hp hq η φ hη θ f

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHomFunctoriality

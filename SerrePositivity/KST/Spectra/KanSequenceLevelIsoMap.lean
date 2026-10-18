module

public import SerrePositivity.KST.Spectra.KanSequenceLevelIso

/-!
概要：段ごとの同型で移送した Kan 列の厳密な同型と射の移送。
方針：構造可換式を各段の同型で相殺し、比較射の逆を作る。
規約：Kan 列の通常の圏での同型であり単射構造射の仮定は不要。
使われ方：HA §1.4.2、BF 1978 §2。通常の Tot の射の構造への整合性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.KanSequence

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : KanSequence.{u}) (Z : ℕ → PointedKanComplex.{u})
    (e : ∀ n, (Z n).space ≅ (X.level n).space)

/-- 概要：移送した列からの段の同型の厳密な逆射。
方針：比較射の構造可換式を同型で左右から相殺する。
規約：各段は指定した点つき同型の逆。
使われ方：HA §1.4.2、BF 1978 §2。Kan 列全体の厳密な同型。 -/
def changeLevelsInverse : Hom X (changeLevels X Z e) where
  app n := (e n).inv
  comm n := by
    apply (cancel_mono (e (n + 1)).hom).mp
    have h : PointedSimplicialSet.circle.{u} ◁ (e n).hom ≫ X.sigma n =
        (changeLevels X Z e).sigma n ≫ (e (n + 1)).hom :=
      (changeLevelsProjection X Z e).comm n
    rw [Category.assoc, ← h]
    change (PointedSimplicialSet.circle.{u} ◁ (e n).inv) ≫
        (PointedSimplicialSet.circle.{u} ◁ (e n).hom ≫ X.sigma n) =
      (X.sigma n ≫ (e (n + 1)).inv) ≫ (e (n + 1)).hom
    rw [← Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id,
      whiskerLeft_id, Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 概要：段の同型による Kan 列の移送は元の列と厳密に同型。
方針：各段の同型と逆同型を列の射へ束ね、各段で両逆を確認する。
規約：通常の Kan 列の圏の同型。
使われ方：HA §1.4.2、BF 1978 §2。段の模型の変更への独立性。 -/
def changeLevelsIso : changeLevels X Z e ≅ X where
  hom := changeLevelsProjection X Z e
  inv := changeLevelsInverse X Z e
  hom_inv_id := by
    apply Hom.ext_app
    intro n
    exact (e n).hom_inv_id
  inv_hom_id := by
    apply Hom.ext_app
    intro n
    exact (e n).inv_hom_id

/-- 概要：Kan 列の射を指定された段の同型で共役する。
方針：源の比較、元の射、標的の逆比較を合成する。
規約：各段の共役と構造射との厳密可換性を持つ。
使われ方：HA §1.4.2、BF 1978 §2。通常の Tot の係数の射の移送。 -/
def changeLevelsMap {X Y : KanSequence.{u}} (Z T : ℕ → PointedKanComplex.{u})
    (e : ∀ n, (Z n).space ≅ (X.level n).space)
    (d : ∀ n, (T n).space ≅ (Y.level n).space) (f : Hom X Y) :
    Hom (changeLevels X Z e) (changeLevels Y T d) :=
  ((changeLevelsProjection X Z e).comp f).comp (changeLevelsInverse Y T d)

lemma changeLevelsMap_app {X Y : KanSequence.{u}} (Z T : ℕ → PointedKanComplex.{u})
    (e : ∀ n, (Z n).space ≅ (X.level n).space)
    (d : ∀ n, (T n).space ≅ (Y.level n).space) (f : Hom X Y) (n : ℕ) :
    (changeLevelsMap Z T e d f).app n = (e n).hom ≫ f.app n ≫ (d n).inv :=
  Category.assoc _ _ _

end

end SerrePositivity.KST.Spectra.KanSequence

module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Maps
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # 自由path Homの連結chain mapと左単位

## 概要
結合則と右単位は後続で検証し、まだEnrichedCategory instanceは宣言しない。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.FreeDGCategory
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

def pathComposition (K : ComplexQuiver A D) {x y z : D}
    (p : PathIndex D x y) (q : PathIndex D y z) :
    pathTensor A D K p ⊗ pathTensor A D K q ⟶ homComplex A D K x z := by
  cases p with
  | inl h =>
    rcases h with ⟨h⟩
    subst y
    exact (λ_ (pathTensor A D K q)).hom ≫ pathInclusion A D K x z q
  | inr w =>
    cases q with
    | inl h =>
      rcases h with ⟨h⟩
      subst z
      exact (ρ_ (wordTensor A D K w x y)).hom ≫ pathInclusion A D K x y (.inr w)
    | inr t =>
      exact (wordConcatenationIso A D K w t x y z).hom ≫
        pathInclusion A D K x z (.inr (concatenate D w t y))

/-- 二つの全path直和を連結する、内部微分に関するchain map。 -/
def composition (K : ComplexQuiver A D) (x y z : D) :
    homComplex A D K x y ⊗ homComplex A D K y z ⟶ homComplex A D K x z :=
  tensorCoproductDesc (pathTensor A D K (x := x) (y := y))
    (pathTensor A D K (x := y) (y := z)) (homComplex A D K x z)
    (pathComposition A D K)

lemma composition_pathInclusion (K : ComplexQuiver A D) (x y z : D)
    (p : PathIndex D x y) (q : PathIndex D y z) :
    (pathInclusion A D K x y p ⊗ₘ pathInclusion A D K y z q) ≫ composition A D K x y z =
      pathComposition A D K p q := tensorCoproductDesc_ι _ _ _ _ p q

lemma composition_nonempty (K : ComplexQuiver A D) (x y z : D) (w t : List D) :
    (pathInclusion A D K x y (.inr w) ⊗ₘ pathInclusion A D K y z (.inr t)) ≫
        composition A D K x y z =
      (wordConcatenationIso A D K w t x y z).hom ≫
        pathInclusion A D K x z (.inr (concatenate D w t y)) :=
  composition_pathInclusion A D K x y z (.inr w) (.inr t)

lemma composition_unit_path (K : ComplexQuiver A D) (x y : D) (p : PathIndex D x y) :
    (unitInclusion A D K x ⊗ₘ pathInclusion A D K x y p) ≫ composition A D K x x y =
      (λ_ (pathTensor A D K p)).hom ≫ pathInclusion A D K x y p :=
  composition_pathInclusion A D K x x y (.inl ⟨rfl⟩) p

lemma composition_left_unit (K : ComplexQuiver A D) (x y : D) :
    (unitInclusion A D K x ▷ homComplex A D K x y) ≫ composition A D K x x y =
      (λ_ (homComplex A D K x y)).hom := by
  apply (tensorLeftCoproductIsColimit (𝟙_ (Complex A))
    (pathTensor A D K (x := x) (y := y))).hom_ext
  rintro ⟨p⟩
  change (𝟙_ (Complex A) ◁ pathInclusion A D K x y p) ≫
      ((unitInclusion A D K x ▷ homComplex A D K x y) ≫ composition A D K x x y) = _
  rw [← Category.assoc, ← tensorHom_def', composition_unit_path]
  exact (leftUnitor_naturality (pathInclusion A D K x y p)).symm

end SerrePositivity.DifferentialGraded.FreeDGCategory

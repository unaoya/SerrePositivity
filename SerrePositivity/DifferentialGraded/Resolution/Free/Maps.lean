module
public import SerrePositivity.DifferentialGraded.Resolution.Free.Hom

/-! # 辺のchain mapによる全path直和の関手性

## 概要
辺のchain mapによる全path直和の関手性。

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
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [Small.{u} D]

/-- 恒等pathを固定し、非空pathを辺ごとのtensor写像で送る。 -/
def pathMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y) {x y : D} :
    ∀ p : PathIndex D x y, pathTensor A D K p ⟶ pathTensor A D L p
  | .inl _ => 𝟙 _
  | .inr w => wordMap A D f w x y

def homMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y) (x y : D) :
    homComplex A D K x y ⟶ homComplex A D L x y :=
  Sigma.desc (fun p => pathMap A D f p ≫ pathInclusion A D L x y p)

lemma pathInclusion_homMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y)
    (x y : D) (p : PathIndex D x y) :
    pathInclusion A D K x y p ≫ homMap A D f x y =
      pathMap A D f p ≫ pathInclusion A D L x y p := Sigma.ι_comp_desc _ _

lemma unitInclusion_homMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y)
    (x : D) : unitInclusion A D K x ≫ homMap A D f x x = unitInclusion A D L x := by
  have h := pathInclusion_homMap A D f x x (.inl ⟨rfl⟩)
  exact h.trans (Category.id_comp _)

lemma edgeInclusion_homMap {K L : ComplexQuiver A D} (f : ∀ x y, K x y ⟶ L x y)
    (x y : D) : edgeInclusion A D K x y ≫ homMap A D f x y =
      f x y ≫ edgeInclusion A D L x y :=
  pathInclusion_homMap A D f x y (.inr [])

omit [Small.{u} D] in
lemma pathMap_id (K : ComplexQuiver A D) {x y : D} (p : PathIndex D x y) :
    pathMap A D (fun x y => 𝟙 (K x y)) p = 𝟙 (pathTensor A D K p) := by
  cases p with
  | inl _ => rfl
  | inr w => exact wordMap_id A D K w x y

omit [Small.{u} D] in
lemma pathMap_comp {K L M : ComplexQuiver A D}
    (f : ∀ x y, K x y ⟶ L x y) (g : ∀ x y, L x y ⟶ M x y)
    {x y : D} (p : PathIndex D x y) :
    pathMap A D (fun x y => f x y ≫ g x y) p = pathMap A D f p ≫ pathMap A D g p := by
  cases p with
  | inl _ => exact (Category.id_comp _).symm
  | inr w => exact wordMap_comp A D f g w x y

lemma homMap_id (K : ComplexQuiver A D) (x y : D) :
    homMap A D (fun x y => 𝟙 (K x y)) x y = 𝟙 (homComplex A D K x y) := by
  apply homComplex_ext A D K x y
  intro p
  rw [pathInclusion_homMap, pathMap_id, Category.id_comp, Category.comp_id]

lemma homMap_comp {K L M : ComplexQuiver A D}
    (f : ∀ x y, K x y ⟶ L x y) (g : ∀ x y, L x y ⟶ M x y) (x y : D) :
    homMap A D (fun x y => f x y ≫ g x y) x y = homMap A D f x y ≫ homMap A D g x y := by
  apply homComplex_ext A D K x y
  intro p
  rw [pathInclusion_homMap, pathMap_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (pathInclusion_homMap A D f x y p), pathInclusion_homMap]

end SerrePositivity.DifferentialGraded.FreeDGCategory

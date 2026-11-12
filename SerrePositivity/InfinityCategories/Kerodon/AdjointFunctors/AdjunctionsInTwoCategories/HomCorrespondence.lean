module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.AdjunctNaturality

/-!
概要：パラメータに自然な二胞体の Hom 対応から双圏随伴を構成する。
方針：恒等二胞体の対応から単位・余単位を取り、自然性で三角恒等式を導く。
規約：三角恒等式を対応の入力の欄には含めない。任意の双圏で証明する。
使われ方：Kerodon §6.1.2（Tag 02CP）、Remark 6.2.1.4（Tag 02EN）、HTT §5.2 の逆向きの代数的な段階。

対応節は Kerodon 6.1（Tag 02CA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Bicategory
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories

/-- 概要：二変数とパラメータに自然な双圏の Hom 対応。
方針：各 Hom の全単射、前後合成自然性、左 whisker の整合を記録する。
規約：単位・余単位や三角恒等式は入力として持たない。
使われ方：写像空間に由来する対応から随伴を構成する中間表示。 -/
@[ext] structure BicategoryHomCorrespondence {B : Type u} [Bicategory.{w, v} B]
    {b c : B} (l : b ⟶ c) (r : c ⟶ b) where
  equiv : ∀ {a : B} (g : a ⟶ b) (h : a ⟶ c), (g ≫ l ⟶ h) ≃ (g ⟶ h ≫ r)
  naturality_right : ∀ {a : B} {g : a ⟶ b} {h h' : a ⟶ c}
    (α : g ≫ l ⟶ h) (β : h ⟶ h'),
    equiv g h' (α ≫ β) = equiv g h α ≫ β ▷ r
  naturality_left : ∀ {a : B} {g g' : a ⟶ b} {h : a ⟶ c}
    (γ : g' ⟶ g) (α : g ≫ l ⟶ h),
    equiv g' h (γ ▷ l ≫ α) = γ ≫ equiv g h α
  precomp : ∀ {a d : B} (i : d ⟶ a) {g : a ⟶ b} {h : a ⟶ c}
    (α : g ≫ l ⟶ h),
    equiv (i ≫ g) (i ≫ h) ((α_ i g l).hom ≫ i ◁ α) =
      i ◁ equiv g h α ≫ (α_ i h r).inv

namespace BicategoryHomCorrespondence
variable {B : Type u} [Bicategory.{w, v} B] {b c : B} {l : b ⟶ c} {r : c ⟶ b}

/-- 概要：自然な Hom 対応から取り出す単位。
方針：左単位子を対応で写す。
規約：単位子を明示し、双圏の厳密性を要求しない。
使われ方：随伴の逆方向の構成。 -/
def unit (e : BicategoryHomCorrespondence l r) : 𝟙 b ⟶ l ≫ r :=
  e.equiv (𝟙 b) l (λ_ l).hom

/-- 概要：自然な Hom 対応から取り出す余単位。
方針：左単位子の逆を逆対応で写す。
規約：余単位の可逆性は要求しない。
使われ方：随伴の逆方向の構成。 -/
def counit (e : BicategoryHomCorrespondence l r) : r ≫ l ⟶ 𝟙 c :=
  (e.equiv r (𝟙 c)).symm (λ_ r).inv

/-- 概要：余単位の像は指定した左単位子の逆。
方針：全単射の両逆の式。
規約：同じ対応 e を用いる。
使われ方：三角恒等式の導出。 -/
lemma counit_spec (e : BicategoryHomCorrespondence l r) :
    e.equiv r (𝟙 c) e.counit = (λ_ r).inv :=
  (e.equiv r (𝟙 c)).apply_symm_apply _

/-- 概要：自然な Hom 対応から構成した単位・余単位の右三角恒等式。
方針：単位の左 whisker をパラメータ自然性で戻し、前後合成自然性を使う。
規約：三角恒等式は仮定せず、全単射の逆則から導く。
使われ方：双圏随伴の構造体を組み立てる。 -/
lemma right_triangle (e : BicategoryHomCorrespondence l r) :
    rightZigzag e.unit e.counit = (ρ_ r).hom ≫ (λ_ r).inv := by
  calc
    _ = (r ◁ e.unit ≫ (α_ r l r).inv) ≫ e.counit ▷ r := by bicategory
    _ = e.equiv (r ≫ 𝟙 b) (r ≫ l) ((α_ r (𝟙 b) l).hom ≫ r ◁ (λ_ l).hom) ≫
        e.counit ▷ r := by rw [e.precomp]; rfl
    _ = e.equiv (r ≫ 𝟙 b) (𝟙 c)
        (((α_ r (𝟙 b) l).hom ≫ r ◁ (λ_ l).hom) ≫ e.counit) :=
      (e.naturality_right _ _).symm
    _ = e.equiv (r ≫ 𝟙 b) (𝟙 c) ((ρ_ r).hom ▷ l ≫ e.counit) := by
      congr 1
      bicategory
    _ = (ρ_ r).hom ≫ e.equiv r (𝟙 c) e.counit := e.naturality_left _ _
    _ = _ := by rw [e.counit_spec]

/-- 概要：自然な Hom 対応から構成した単位・余単位の左三角恒等式。
方針：全単射の単射性で写した後、始域自然性と余単位のパラメータ自然性を使う。
規約：非厳密な双圏の単位子・結合子も保つ。
使われ方：双圏随伴の構造体を組み立てる。 -/
lemma left_triangle (e : BicategoryHomCorrespondence l r) :
    leftZigzag e.unit e.counit = (λ_ l).hom ≫ (ρ_ l).inv := by
  apply (e.equiv (𝟙 b) (l ≫ 𝟙 c)).injective
  calc
    _ = e.equiv (𝟙 b) (l ≫ 𝟙 c)
        (e.unit ▷ l ≫ ((α_ l r l).hom ≫ l ◁ e.counit)) := by
      congr 1
      bicategory
    _ = e.unit ≫ e.equiv (l ≫ r) (l ≫ 𝟙 c) ((α_ l r l).hom ≫ l ◁ e.counit) :=
      e.naturality_left _ _
    _ = e.unit ≫ (l ◁ e.equiv r (𝟙 c) e.counit ≫ (α_ l (𝟙 c) r).inv) := by
      rw [e.precomp]
    _ = e.unit ≫ (l ◁ (λ_ r).inv ≫ (α_ l (𝟙 c) r).inv) := by rw [e.counit_spec]
    _ = e.unit ≫ (ρ_ l).inv ▷ r := by bicategory
    _ = e.equiv (𝟙 b) l (λ_ l).hom ≫ (ρ_ l).inv ▷ r := rfl
    _ = e.equiv (𝟙 b) (l ≫ 𝟙 c) ((λ_ l).hom ≫ (ρ_ l).inv) :=
      (e.naturality_right _ _).symm

/-- 概要：自然な二胞体の Hom 対応から随伴を構成する。
方針：取り出した単位・余単位と、導出した二つの三角恒等式を束ねる。
規約：対応の自然性が入力であり、随伴の結論は入力に含まない。
使われ方：Kerodon Remark 6.2.1.4（Tag 02EN） の随伴を得る代数的な逆方向。 -/
def toAdjunction (e : BicategoryHomCorrespondence l r) : Bicategory.Adjunction l r where
  unit := e.unit
  counit := e.counit
  left_triangle := e.left_triangle
  right_triangle := e.right_triangle

/-- 概要：随伴が与える自然な二胞体の Hom 対応。
方針：既存の homEquiv₂ と三つの自然性の補題を使う。
規約：任意の双圏。
使われ方：対応と単位・余単位の特徴づけの順方向。 -/
def ofAdjunction (a : Bicategory.Adjunction l r) : BicategoryHomCorrespondence l r where
  equiv _ _ := a.homEquiv₂
  naturality_right := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.bicategoryAdjunct_naturality_right a
  naturality_left := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.bicategoryAdjunct_naturality_left a
  precomp := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.bicategoryAdjunct_whiskerLeft a

/-- 概要：対応から得た随伴の adjunct は元の対応と一致する。
方針：単位のパラメータ自然性、始域の右単位子の自然性、終域自然性を使う。
規約：任意の g,h の全単射そのものの一致。
使われ方：自然な Hom 対応による随伴の特徴づけの往復。 -/
lemma toAdjunction_homEquiv (e : BicategoryHomCorrespondence l r)
    {a : B} (g : a ⟶ b) (h : a ⟶ c) :
    e.toAdjunction.homEquiv₂ (g := g) (h := h) = e.equiv g h := by
  apply Equiv.ext
  intro α
  symm
  calc
    e.equiv g h α = (ρ_ g).inv ≫ ((ρ_ g).hom ≫ e.equiv g h α) := by simp
    _ = (ρ_ g).inv ≫ e.equiv (g ≫ 𝟙 b) h
        (((α_ g (𝟙 b) l).hom ≫ g ◁ (λ_ l).hom) ≫ α) := by
      have hc : (α_ g (𝟙 b) l).hom ≫ g ◁ (λ_ l).hom = (ρ_ g).hom ▷ l := by
        bicategory
      rw [hc, e.naturality_left]
    _ = (ρ_ g).inv ≫
        (e.equiv (g ≫ 𝟙 b) (g ≫ l) ((α_ g (𝟙 b) l).hom ≫ g ◁ (λ_ l).hom) ≫ α ▷ r) := by
      rw [e.naturality_right]
    _ = (ρ_ g).inv ≫ ((g ◁ e.unit ≫ (α_ g l r).inv) ≫ α ▷ r) := by
      rw [e.precomp]
      rfl
    _ = _ := by
      dsimp only [toAdjunction, Bicategory.Adjunction.homEquiv₂, Equiv.coe_fn_mk]
      simp only [Category.assoc]

/-- 概要：随伴から対応を取り出して構成し直すと元の随伴。
方針：単位・余単位の公式と双圏の coherence を計算する。
規約：単位・余単位を含む構造体の等式。
使われ方：Hom 対応による随伴の特徴づけの逆の往復。 -/
lemma ofAdjunction_toAdjunction (a : Bicategory.Adjunction l r) :
    (ofAdjunction a).toAdjunction = a := by
  apply Bicategory.Adjunction.ext
  · dsimp only [toAdjunction, unit, ofAdjunction, Bicategory.Adjunction.homEquiv₂,
      Equiv.coe_fn_mk]
    bicategory
  · dsimp only [toAdjunction, counit, ofAdjunction, Bicategory.Adjunction.homEquiv₂,
      Equiv.symm_apply_apply, Equiv.coe_fn_symm_mk]
    bicategory

/-- 概要：自然な Hom 対応と双圏随伴のデータは全単射。
方針：構成と回収の二つの往復を使う。
規約：三角条件を対応の側に持たせない。
使われ方：quasicategory の二胞体の表示に移す代数的な特徴づけ。 -/
def adjunctionEquiv : BicategoryHomCorrespondence l r ≃ Bicategory.Adjunction l r where
  toFun := toAdjunction
  invFun := ofAdjunction
  left_inv e := by
    apply BicategoryHomCorrespondence.ext
    funext a g h
    exact e.toAdjunction_homEquiv g h
  right_inv := ofAdjunction_toAdjunction

end BicategoryHomCorrespondence
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories

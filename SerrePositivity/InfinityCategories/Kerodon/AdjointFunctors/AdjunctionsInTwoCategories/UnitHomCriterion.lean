module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.HomCorrespondence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：指定された単位による Hom 対応の全単射性から双圏随伴を構成する。
方針：単位の公式だけから三つの自然性を導き、自然な対応の構成定理を使う。
規約：全てのパラメータ・一胞体の Hom に関する条件。点ごとの π₀ 条件と同一視しない。
使われ方：Kerodon Cor 6.2.6.5（Tag 02FX） の指定単位による判定の代数的な段階。

対応節は Kerodon 6.1（Tag 02CA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory Bicategory
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories

/-- 概要：指定した単位が誘導する二胞体の Hom 写像。
方針：単位を左 whisker し、与えられた二胞体を右 whisker して続ける。
規約：三角恒等式・余単位・全単射性は仮定しない。
使われ方：写像空間の単位による比較を二胞体レベルに表示する。 -/
def bicategoryUnitHomMap {B : Type u} [Bicategory.{w, v} B]
    {a b c : B} {l : b ⟶ c} {r : c ⟶ b} (η : 𝟙 b ⟶ l ≫ r)
    (g : a ⟶ b) (h : a ⟶ c) (α : g ≫ l ⟶ h) : g ⟶ h ≫ r :=
  (ρ_ g).inv ≫ g ◁ η ≫ (α_ g l r).inv ≫ α ▷ r

/-- 概要：単位による Hom 写像は終域側の合成に自然。
方針：右 whisker の合成保存と結合則。
規約：任意の単位候補に対して成立する。
使われ方：全単射から自然な Hom 対応を組み立てる。 -/
lemma bicategoryUnitHomMap_naturality_right {B : Type u} [Bicategory.{w, v} B]
    {a b c : B} {l : b ⟶ c} {r : c ⟶ b} (η : 𝟙 b ⟶ l ≫ r)
    {g : a ⟶ b} {h h' : a ⟶ c} (α : g ≫ l ⟶ h) (β : h ⟶ h') :
    bicategoryUnitHomMap η g h' (α ≫ β) = bicategoryUnitHomMap η g h α ≫ β ▷ r := by
  simp [bicategoryUnitHomMap, Category.assoc]

/-- 概要：単位による Hom 写像は始域側の合成に自然。
方針：結合子の自然性、交換則、右単位子の自然性を使う。
規約：任意の単位候補に対して成立する。
使われ方：全単射から自然な Hom 対応を組み立てる。 -/
lemma bicategoryUnitHomMap_naturality_left {B : Type u} [Bicategory.{w, v} B]
    {a b c : B} {l : b ⟶ c} {r : c ⟶ b} (η : 𝟙 b ⟶ l ≫ r)
    {g g' : a ⟶ b} {h : a ⟶ c} (γ : g' ⟶ g) (α : g ≫ l ⟶ h) :
    bicategoryUnitHomMap η g' h (γ ▷ l ≫ α) = γ ≫ bicategoryUnitHomMap η g h α := by
  simp only [bicategoryUnitHomMap, Bicategory.comp_whiskerRight]
  rw [← Bicategory.associator_inv_naturality_left_assoc]
  rw [Bicategory.whisker_exchange_assoc]
  rw [← Bicategory.rightUnitor_inv_naturality_assoc]

/-- 概要：単位による Hom 写像はパラメータの左 whisker に自然。
方針：単位子と結合子の coherence を使う。
規約：任意の単位候補に対して成立する。
使われ方：全単射から自然な Hom 対応を組み立てる。 -/
lemma bicategoryUnitHomMap_precomp {B : Type u} [Bicategory.{w, v} B]
    {a b c d : B} {l : b ⟶ c} {r : c ⟶ b} (η : 𝟙 b ⟶ l ≫ r)
    (i : d ⟶ a) {g : a ⟶ b} {h : a ⟶ c} (α : g ≫ l ⟶ h) :
    bicategoryUnitHomMap η (i ≫ g) (i ≫ h) ((α_ i g l).hom ≫ i ◁ α) =
      i ◁ bicategoryUnitHomMap η g h α ≫ (α_ i h r).inv := by
  unfold bicategoryUnitHomMap
  bicategory

namespace BicategoryHomCorrespondence
variable {B : Type u} [Bicategory.{w, v} B] {b c : B} {l : b ⟶ c} {r : c ⟶ b}

/-- 概要：単位が誘導する全単射を自然な Hom 対応にする。
方針：全単射の逆を選び、単位の公式から導いた自然性を付ける。
規約：条件は全てのパラメータの二胞体について課す。
使われ方：指定単位を持つ随伴の構成。 -/
noncomputable def ofUnit (η : 𝟙 b ⟶ l ≫ r)
    (hη : ∀ {a : B} (g : a ⟶ b) (h : a ⟶ c),
      Function.Bijective (bicategoryUnitHomMap η g h)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.BicategoryHomCorrespondence l r where
  equiv g h := Equiv.ofBijective _ (hη g h)
  naturality_right := bicategoryUnitHomMap_naturality_right η
  naturality_left := bicategoryUnitHomMap_naturality_left η
  precomp := bicategoryUnitHomMap_precomp η

/-- 概要：単位の全単射から構成した対応の単位は指定された η。
方針：左単位子の像を単位の公式で計算する。
規約：単位の同型による一致ではなく二胞体の等式。
使われ方：指定単位を持つ随伴の存在判定。 -/
lemma ofUnit_unit (η : 𝟙 b ⟶ l ≫ r)
    (hη : ∀ {a : B} (g : a ⟶ b) (h : a ⟶ c),
      Function.Bijective (bicategoryUnitHomMap η g h)) : (ofUnit η hη).unit = η := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories.BicategoryHomCorrespondence.unit, ofUnit, Equiv.ofBijective, Equiv.coe_fn_mk, bicategoryUnitHomMap]
  bicategory

end BicategoryHomCorrespondence

/-- 概要：単位による全ての Hom 写像が全単射なら指定単位を持つ随伴が存在する。
方針：自然な対応を構成し、その三角恒等式の定理を適用する。
規約：余単位と三角恒等式は結論として構成する。
使われ方：quasicategory の写像空間の単位判定へ接続する代数的な終点。 -/
@[kerodon 02CY]
noncomputable def bicategoryAdjunctionOfUnitHomBijective {B : Type u} [Bicategory.{w, v} B]
    {b c : B} {l : b ⟶ c} {r : c ⟶ b} (η : 𝟙 b ⟶ l ≫ r)
    (hη : ∀ {a : B} (g : a ⟶ b) (h : a ⟶ c),
      Function.Bijective (bicategoryUnitHomMap η g h)) : Bicategory.Adjunction l r :=
  (BicategoryHomCorrespondence.ofUnit η hη).toAdjunction

/-- 概要：全単射条件から構成した随伴は指定された単位を持つ。
方針：自然な対応の単位の回収を使う。
規約：二胞体の等式。
使われ方：二胞体の表示同値で単位の等式を移す。 -/
lemma bicategoryAdjunctionOfUnitHomBijective_unit {B : Type u} [Bicategory.{w, v} B]
    {b c : B} {l : b ⟶ c} {r : c ⟶ b} (η : 𝟙 b ⟶ l ≫ r)
    (hη : ∀ {a : B} (g : a ⟶ b) (h : a ⟶ c),
      Function.Bijective (bicategoryUnitHomMap η g h)) :
    (bicategoryAdjunctionOfUnitHomBijective η hη).unit = η :=
  BicategoryHomCorrespondence.ofUnit_unit η hη

/-- 概要：指定単位を持つ随伴と全パラメータでの Hom 全単射条件は同値。
方針：順方向は adjunct の全単射、逆方向は上の構成と単位の回収を使う。
規約：対象ごとの Hom だけの条件には弱めない。
使われ方：指定単位による特徴づけの代数的な判定。 -/
@[kerodon 02CY, kerodon 02CZ]
lemma bicategory_exists_adjunction_unit_iff {B : Type u} [Bicategory.{w, v} B]
    {b c : B} {l : b ⟶ c} {r : c ⟶ b} (η : 𝟙 b ⟶ l ≫ r) :
    (∃ a : Bicategory.Adjunction l r, a.unit = η) ↔
      ∀ {a : B} (g : a ⟶ b) (h : a ⟶ c),
        Function.Bijective (bicategoryUnitHomMap η g h) := by
  constructor
  · rintro ⟨a, rfl⟩ A g h
    exact (a.homEquiv₂ (g := g) (h := h)).bijective
  · intro hη
    exact ⟨bicategoryAdjunctionOfUnitHomBijective η hη,
      BicategoryHomCorrespondence.ofUnit_unit η hη⟩

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjunctionsInTwoCategories

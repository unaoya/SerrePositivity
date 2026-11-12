module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTransform
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
概要：パラメーターを右直積に持つ fat join の普遍性。
方針：対称性と内部 Hom の随伴でパラメーターを標的に移して貼り合わせる。
規約：パラメーター集合の quasicategory 性は不要。
使われ方：Kerodon §4.6.2（Tag 01HM） の標準単体の変形のホモトピー。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed BraidedCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：右の直積のパラメーターを内部 Hom に移す curry。
方針：対称性の後に既存の curry を適用する。
規約：第一因子 Y が結果の始域となる。
使われ方：Kerodon §4.6.2（Tag 01HM） のパラメーターを持つ貼り合わせ。 -/
def curryTensorRight {Y T X : SSet.{u}} (H : Y ⊗ T ⟶ X) : Y ⟶ (ihom T).obj X :=
  curry ((β_ T Y).hom ≫ H)

/-- 概要：右のパラメーターの curry は始域の射に自然。
方針：対称性の自然性と curry の自然性を使う。
規約：厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の端点の整合条件。 -/
lemma curryTensorRight_natural_left {Y Z T X : SSet.{u}} (f : Y ⟶ Z) (H : Z ⊗ T ⟶ X) :
    curryTensorRight ((f ▷ T) ≫ H) = f ≫ curryTensorRight H := by
  unfold curryTensorRight
  rw [← curry_natural_left, braiding_naturality_right_assoc]

/-- 概要：内部 Hom の射を右の直積のパラメーターを持つ射に戻す。
方針：uncurry の後の入力を対称性で交換する。
規約：curryTensorRight の逆。
使われ方：Kerodon §4.6.2（Tag 01HM） のパラメーターを持つ貼り合わせ。 -/
def uncurryTensorRight {Y T X : SSet.{u}} (F : Y ⟶ (ihom T).obj X) : Y ⊗ T ⟶ X :=
  (β_ Y T).hom ≫ uncurry F

/-- 概要：右のパラメーターで curry して戻すと元の射になる。
方針：curry と uncurry の逆性と対称性を使う。
規約：任意の単体集合の射。
使われ方：Kerodon §4.6.2（Tag 01HM） の貼り合わせの制限の計算。 -/
lemma uncurryTensorRight_curryTensorRight {Y T X : SSet.{u}} (H : Y ⊗ T ⟶ X) :
    uncurryTensorRight (curryTensorRight H) = H := by
  unfold uncurryTensorRight curryTensorRight
  rw [uncurry_curry, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]

/-- 概要：右のパラメーターを戻す操作も始域の射に自然。
方針：対称性と uncurry の自然性を使う。
規約：厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の円柱と左右の因子の制限。 -/
lemma uncurryTensorRight_natural_left {Y Z T X : SSet.{u}}
    (f : Y ⟶ Z) (F : Z ⟶ (ihom T).obj X) :
    uncurryTensorRight (f ≫ F) = (f ▷ T) ≫ uncurryTensorRight F := by
  unfold uncurryTensorRight
  rw [uncurry_natural_left, ← braiding_naturality_left_assoc]

/-- 概要：パラメーターを持つ左右の因子と円柱の射を fat join 上へ貼る。
方針：パラメーターを内部 Hom に移して既存の普遍性を使う。
規約：両端の一致はパラメーターも含む厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の変形のホモトピーの構成。 -/
noncomputable def fatJoinDescTensorRight {A B T X : SSet.{u}}
    (f : A ⊗ T ⟶ X) (g : B ⊗ T ⟶ X)
    (H : ((A ⊗ (Δ[1] : SSet.{u})) ⊗ B) ⊗ T ⟶ X)
    (h₀ : ((SSet.ι₀ (X := A) ▷ B) ▷ T) ≫ H = (CartesianMonoidalCategory.fst A B ▷ T) ≫ f)
    (h₁ : ((SSet.ι₁ (X := A) ▷ B) ▷ T) ≫ H = (CartesianMonoidalCategory.snd A B ▷ T) ≫ g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ⊗ T ⟶ X :=
  uncurryTensorRight (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc (curryTensorRight f) (curryTensorRight g)
    (curryTensorRight H)
    (by rw [← curryTensorRight_natural_left, h₀, curryTensorRight_natural_left])
    (by rw [← curryTensorRight_natural_left, h₁, curryTensorRight_natural_left]))

/-- 概要：パラメーター付きの貼り合わせは円柱上で指定された射に一致する。
方針：uncurry の自然性と通常の fat join の計算を使う。
規約：固定条件は貼り合わせの定義と同じ。
使われ方：Kerodon §4.6.2（Tag 01HM） のホモトピーの式の確認。 -/
lemma fatJoinCylinder_descTensorRight {A B T X : SSet.{u}}
    (f : A ⊗ T ⟶ X) (g : B ⊗ T ⟶ X)
    (H : ((A ⊗ (Δ[1] : SSet.{u})) ⊗ B) ⊗ T ⟶ X)
    (h₀ : ((SSet.ι₀ (X := A) ▷ B) ▷ T) ≫ H = (CartesianMonoidalCategory.fst A B ▷ T) ≫ f)
    (h₁ : ((SSet.ι₁ (X := A) ▷ B) ▷ T) ≫ H = (CartesianMonoidalCategory.snd A B ▷ T) ≫ g) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ▷ T) ≫ fatJoinDescTensorRight f g H h₀ h₁ = H := by
  unfold fatJoinDescTensorRight
  rw [← uncurryTensorRight_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc,
    uncurryTensorRight_curryTensorRight]

/-- 概要：パラメーター付きの貼り合わせは左因子上で指定された射になる。
方針：uncurry の自然性と左包含の計算を使う。
規約：パラメーターは右側の直積。
使われ方：Kerodon §4.6.2（Tag 01HM） のホモトピーの頂点の固定。 -/
lemma fatJoinInl_descTensorRight {A B T X : SSet.{u}}
    (f : A ⊗ T ⟶ X) (g : B ⊗ T ⟶ X)
    (H : ((A ⊗ (Δ[1] : SSet.{u})) ⊗ B) ⊗ T ⟶ X)
    (h₀ : ((SSet.ι₀ (X := A) ▷ B) ▷ T) ≫ H = (CartesianMonoidalCategory.fst A B ▷ T) ≫ f)
    (h₁ : ((SSet.ι₁ (X := A) ▷ B) ▷ T) ≫ H = (CartesianMonoidalCategory.snd A B ▷ T) ≫ g) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ▷ T) ≫ fatJoinDescTensorRight f g H h₀ h₁ = f := by
  unfold fatJoinDescTensorRight
  rw [← uncurryTensorRight_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc,
    uncurryTensorRight_curryTensorRight]

/-- 概要：パラメーター付きの貼り合わせは右因子上で指定された射になる。
方針：uncurry の自然性と右包含の計算を使う。
規約：パラメーターは右側の直積。
使われ方：Kerodon §4.6.2（Tag 01HM） のホモトピーの頂点の固定。 -/
lemma fatJoinInr_descTensorRight {A B T X : SSet.{u}}
    (f : A ⊗ T ⟶ X) (g : B ⊗ T ⟶ X)
    (H : ((A ⊗ (Δ[1] : SSet.{u})) ⊗ B) ⊗ T ⟶ X)
    (h₀ : ((SSet.ι₀ (X := A) ▷ B) ▷ T) ≫ H = (CartesianMonoidalCategory.fst A B ▷ T) ≫ f)
    (h₁ : ((SSet.ι₁ (X := A) ▷ B) ▷ T) ≫ H = (CartesianMonoidalCategory.snd A B ▷ T) ≫ g) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ▷ T) ≫ fatJoinDescTensorRight f g H h₀ h₁ = g := by
  unfold fatJoinDescTensorRight
  rw [← uncurryTensorRight_natural_left, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc,
    uncurryTensorRight_curryTensorRight]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

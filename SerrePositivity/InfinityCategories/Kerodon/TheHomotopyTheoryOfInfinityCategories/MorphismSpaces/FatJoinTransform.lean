module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinFunctor

/-!
概要：fat join の円柱の時間を保つ左右成分の変換。
方針：零端の左成分と一端の右成分を固定する変換を pushout に降ろす。
規約：時間座標は標準区間の座標をそのまま保つ。
使われ方：Kerodon §4.6.2（Tag 01HM） の標準単体の fat join の変形。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：円柱の零端の射は fat join で左成分にのみ依存する。
方針：直積への lift と零端の包含の可換性を使う。
規約：パラメーター集合 T は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の零端の変形の整合性。 -/
lemma fatJoinCylinder_lift_zero {A B T : SSet.{u}} (f : T ⟶ A) (g : T ⟶ B) :
    lift (f ≫ SSet.ι₀) g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B := by
  rw [← lift_whiskerRight, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_zero,
    ← Category.assoc, lift_fst]

/-- 概要：円柱の一端の射は fat join で右成分にのみ依存する。
方針：直積への lift と一端の包含の可換性を使う。
規約：パラメーター集合 T は任意。
使われ方：Kerodon §4.6.2（Tag 01HM） の一端の変形の整合性。 -/
lemma fatJoinCylinder_lift_one {A B T : SSet.{u}} (f : T ⟶ A) (g : T ⟶ B) :
    lift (f ≫ SSet.ι₁) g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B = g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B := by
  rw [← lift_whiskerRight, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_one,
    ← Category.assoc, lift_snd]

/-- 概要：時間を保って左右の成分を変換する円柱の自己射。
方針：左右の成分に同じ区間座標を渡す。
規約：f と g はそれぞれ標準区間でパラメーター付けられた自己射。
使われ方：Kerodon §4.6.2（Tag 01HM） の二つの正規化。 -/
def fatJoinTransformCylinder {A B : SSet.{u}}
    (f : A ⊗ (Δ[1] : SSet.{u}) ⟶ A) (g : B ⊗ (Δ[1] : SSet.{u}) ⟶ B) :
    (A ⊗ (Δ[1] : SSet.{u})) ⊗ B ⟶ (A ⊗ (Δ[1] : SSet.{u})) ⊗ B :=
  lift (lift (fst (A ⊗ Δ[1]) B ≫ f) (fst (A ⊗ Δ[1]) B ≫ snd A Δ[1]))
    (lift (snd (A ⊗ Δ[1]) B) (fst (A ⊗ Δ[1]) B ≫ snd A Δ[1]) ≫ g)

/-- 概要：零端の左成分を固定する変換は fat join の零端を保つ。
方針：零端への lift の形に直して、右成分を忘れる等式を使う。
規約：g の零端には条件を課さない。
使われ方：Kerodon §4.6.2（Tag 01HM） の正規化の貼り合わせ。 -/
lemma fatJoinTransformCylinder_zero {A B : SSet.{u}}
    (f : A ⊗ (Δ[1] : SSet.{u}) ⟶ A) (g : B ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (hf : SSet.ι₀ ≫ f = 𝟙 A) :
    (SSet.ι₀ (X := A) ▷ B) ≫ fatJoinTransformCylinder f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B =
      fst A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B := by
  have he : (SSet.ι₀ (X := A) ▷ B) ≫ fatJoinTransformCylinder f g =
      lift (fst A B ≫ SSet.ι₀) (snd A B ≫ SSet.ι₀ ≫ g) := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b⟩
    apply Prod.ext
    · apply Prod.ext
      · exact ConcreteCategory.congr_hom (NatTrans.congr_app hf (Opposite.op ⦋n⦌)) a
      · rfl
    · rfl
  rw [← Category.assoc, he, fatJoinCylinder_lift_zero]

/-- 概要：一端の右成分を固定する変換は fat join の一端を保つ。
方針：一端への lift の形に直して、左成分を忘れる等式を使う。
規約：f の一端には条件を課さない。
使われ方：Kerodon §4.6.2（Tag 01HM） の正規化の貼り合わせ。 -/
lemma fatJoinTransformCylinder_one {A B : SSet.{u}}
    (f : A ⊗ (Δ[1] : SSet.{u}) ⟶ A) (g : B ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (hg : SSet.ι₁ ≫ g = 𝟙 B) :
    (SSet.ι₁ (X := A) ▷ B) ≫ fatJoinTransformCylinder f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B =
      snd A B ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B := by
  have he : (SSet.ι₁ (X := A) ▷ B) ≫ fatJoinTransformCylinder f g =
      lift ((fst A B ≫ SSet.ι₁ ≫ f) ≫ SSet.ι₁) (snd A B) := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨a, b⟩
    apply Prod.ext
    · rfl
    · exact ConcreteCategory.congr_hom (NatTrans.congr_app hg (Opposite.op ⦋n⦌)) b
  rw [← Category.assoc, he, fatJoinCylinder_lift_one]

/-- 概要：左右の因子を固定する円柱の変換を fat join の自己射に降ろす。
方針：両端の整合条件を用いて二段の pushout に貼り合わせる。
規約：零端の f と一端の g だけが恒等であることを要求する。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） の標準単体の変形。 -/
noncomputable def fatJoinTransform {A B : SSet.{u}}
    (f : A ⊗ (Δ[1] : SSet.{u}) ⟶ A) (g : B ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (hf : SSet.ι₀ ≫ f = 𝟙 A) (hg : SSet.ι₁ ≫ g = 𝟙 B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B)
    (fatJoinTransformCylinder f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B)
    (fatJoinTransformCylinder_zero f g hf) (fatJoinTransformCylinder_one f g hg)

/-- 概要：変換の fat join の円柱上の制限は指定された変換になる。
方針：pushout による貼り合わせの円柱上の計算を使う。
規約：両端の固定条件は変換の定義と同じ。
使われ方：Kerodon §4.6.2（Tag 01HM） のホモトピーの端点の計算。 -/
lemma fatJoinCylinder_transform {A B : SSet.{u}}
    (f : A ⊗ (Δ[1] : SSet.{u}) ⟶ A) (g : B ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (hf : SSet.ι₀ ≫ f = 𝟙 A) (hg : SSet.ι₁ ≫ g = 𝟙 B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ≫ fatJoinTransform f g hf hg =
      fatJoinTransformCylinder f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc _ _ _ _ _

/-- 概要：円柱の変換は fat join の左因子を固定する。
方針：貼り合わせの左包含上の計算を使う。
規約：端点の固定条件は変換の定義と同じ。
使われ方：Kerodon §4.6.2（Tag 01HM） の変形の頂点の固定。 -/
lemma fatJoinInl_transform {A B : SSet.{u}}
    (f : A ⊗ (Δ[1] : SSet.{u}) ⟶ A) (g : B ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (hf : SSet.ι₀ ≫ f = 𝟙 A) (hg : SSet.ι₁ ≫ g = 𝟙 B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ≫ fatJoinTransform f g hf hg = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc _ _ _ _ _

/-- 概要：円柱の変換は fat join の右因子を固定する。
方針：貼り合わせの右包含上の計算を使う。
規約：端点の固定条件は変換の定義と同じ。
使われ方：Kerodon §4.6.2（Tag 01HM） の変形の頂点の固定。 -/
lemma fatJoinInr_transform {A B : SSet.{u}}
    (f : A ⊗ (Δ[1] : SSet.{u}) ⟶ A) (g : B ⊗ (Δ[1] : SSet.{u}) ⟶ B)
    (hf : SSet.ι₀ ≫ f = 𝟙 A) (hg : SSet.ι₁ ≫ g = 𝟙 B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ≫ fatJoinTransform f g hf hg = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

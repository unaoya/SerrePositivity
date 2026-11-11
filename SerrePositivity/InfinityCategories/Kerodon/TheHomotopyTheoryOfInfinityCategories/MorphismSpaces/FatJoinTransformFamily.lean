module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinTensorDesc

/-!
概要：パラメーター付きの fat join の円柱変換。
方針：区間座標を保ち、左右の成分の時間付きの変形をパラメーター付きの普遍性で貼る。
規約：全てのパラメーターで零端の左成分と一端の右成分を固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の標準単体の二つの変形。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：パラメーターを持ち時間を保つ左右の円柱成分の変換。
方針：左右の写像に同じ元の区間座標とパラメーターを渡す。
規約：始域は元の円柱と T の右直積。
使われ方：Kerodon §4.6.2（Tag 01HM） の正規化のホモトピー。 -/
def fatJoinTransformFamilyCylinder {A B T : SSet.{u}}
    (f : (A ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ A)
    (g : (B ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ B) :
    ((A ⊗ (Δ[1] : SSet.{u})) ⊗ B) ⊗ T ⟶ (A ⊗ (Δ[1] : SSet.{u})) ⊗ B :=
  lift (lift ((fst (A ⊗ Δ[1]) B ▷ T) ≫ f)
      (fst ((A ⊗ Δ[1]) ⊗ B) T ≫ fst (A ⊗ Δ[1]) B ≫ snd A Δ[1]))
    (lift (lift (fst ((A ⊗ Δ[1]) ⊗ B) T ≫ snd (A ⊗ Δ[1]) B)
        (fst ((A ⊗ Δ[1]) ⊗ B) T ≫ fst (A ⊗ Δ[1]) B ≫ snd A Δ[1]))
      (snd ((A ⊗ Δ[1]) ⊗ B) T) ≫ g)

/-- 概要：零端を固定するパラメーター付きの変換は fat join の零端と整合する。
方針：零端への lift の形に直して右成分を忘れる。
規約：g の零端には条件を課さない。
使われ方：Kerodon §4.6.2（Tag 01HM） のホモトピーの貼り合わせ。 -/
lemma fatJoinTransformFamilyCylinder_zero {A B T : SSet.{u}}
    (f : (A ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ A)
    (g : (B ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ B)
    (hf : (SSet.ι₀ (X := A) ▷ T) ≫ f = fst A T) :
    ((SSet.ι₀ (X := A) ▷ B) ▷ T) ≫
        (fatJoinTransformFamilyCylinder f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B) =
      (fst A B ▷ T) ≫ (fst A T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B) := by
  let k := fatJoinTransformFamilyCylinder f g
  let z := ((SSet.ι₀ (X := A) ▷ B) ▷ T)
  have he : z ≫ k = lift ((fst (A ⊗ B) T ≫ fst A B) ≫ SSet.ι₀)
      (z ≫ k ≫ snd (A ⊗ Δ[1]) B) := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, b⟩, t⟩
    apply Prod.ext
    · apply Prod.ext
      · exact congrArg (fun h : A ⊗ T ⟶ A ↦ h.app (Opposite.op ⦋n⦌) (a, t)) hf
      · rfl
    · rfl
  change z ≫ (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B) = _
  rw [← Category.assoc, he, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_zero]
  rfl

/-- 概要：一端を固定するパラメーター付きの変換は fat join の一端と整合する。
方針：一端への lift の形に直して左成分を忘れる。
規約：f の一端には条件を課さない。
使われ方：Kerodon §4.6.2（Tag 01HM） のホモトピーの貼り合わせ。 -/
lemma fatJoinTransformFamilyCylinder_one {A B T : SSet.{u}}
    (f : (A ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ A)
    (g : (B ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ B)
    (hg : (SSet.ι₁ (X := B) ▷ T) ≫ g = fst B T) :
    ((SSet.ι₁ (X := A) ▷ B) ▷ T) ≫
        (fatJoinTransformFamilyCylinder f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B) =
      (snd A B ▷ T) ≫ (fst B T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B) := by
  let k := fatJoinTransformFamilyCylinder f g
  let z := ((SSet.ι₁ (X := A) ▷ B) ▷ T)
  have he : z ≫ k = lift ((z ≫ k ≫ fst (A ⊗ Δ[1]) B ≫ fst A Δ[1]) ≫ SSet.ι₁)
      (fst (A ⊗ B) T ≫ snd A B) := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨a, b⟩, t⟩
    apply Prod.ext
    · rfl
    · exact congrArg (fun h : B ⊗ T ⟶ B ↦ h.app (Opposite.op ⦋n⦌) (b, t)) hg
  change z ≫ (k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B) = _
  rw [← Category.assoc, he, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_lift_one]
  rfl

/-- 概要：左右の端点を固定する円柱変換の族を fat join に降ろす。
方針：パラメーター付きの fat join の普遍性を適用する。
規約：T は任意の単体集合。
使われ方：Kerodon Theorem 4.6.2.8（Tag 01HV） のホモトピー。 -/
noncomputable def fatJoinTransformFamily {A B T : SSet.{u}}
    (f : (A ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ A)
    (g : (B ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ B)
    (hf : (SSet.ι₀ (X := A) ▷ T) ≫ f = fst A T)
    (hg : (SSet.ι₁ (X := B) ▷ T) ≫ g = fst B T) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B ⊗ T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin A B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDescTensorRight (fst A T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B) (fst B T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B)
    (fatJoinTransformFamilyCylinder f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B)
    (fatJoinTransformFamilyCylinder_zero f g hf) (fatJoinTransformFamilyCylinder_one f g hg)

/-- 概要：変換の族の円柱上の制限は元の変換の族。
方針：パラメーター付きの普遍性の円柱上の等式を使う。
規約：パラメーターは右の直積。
使われ方：Kerodon §4.6.2（Tag 01HM） のホモトピーの端点の計算。 -/
lemma fatJoinCylinder_transformFamily {A B T : SSet.{u}}
    (f : (A ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ A)
    (g : (B ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ B)
    (hf : (SSet.ι₀ (X := A) ▷ T) ≫ f = fst A T)
    (hg : (SSet.ι₁ (X := B) ▷ T) ≫ g = fst B T) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B ▷ T) ≫ fatJoinTransformFamily f g hf hg =
      fatJoinTransformFamilyCylinder f g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder A B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_descTensorRight _ _ _ _ _

/-- 概要：変換の族は左因子の上で恒等の族。
方針：パラメーター付きの普遍性の左包含の計算を使う。
規約：時間を含む全てのパラメーターで固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） のホモトピーの可逆性。 -/
lemma fatJoinInl_transformFamily {A B T : SSet.{u}}
    (f : (A ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ A)
    (g : (B ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ B)
    (hf : (SSet.ι₀ (X := A) ▷ T) ≫ f = fst A T)
    (hg : (SSet.ι₁ (X := B) ▷ T) ≫ g = fst B T) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B ▷ T) ≫ fatJoinTransformFamily f g hf hg = fst A T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl A B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_descTensorRight _ _ _ _ _

/-- 概要：変換の族は右因子の上で恒等の族。
方針：パラメーター付きの普遍性の右包含の計算を使う。
規約：時間を含む全てのパラメーターで固定する。
使われ方：Kerodon §4.6.2（Tag 01HM） のホモトピーの可逆性。 -/
lemma fatJoinInr_transformFamily {A B T : SSet.{u}}
    (f : (A ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ A)
    (g : (B ⊗ (Δ[1] : SSet.{u})) ⊗ T ⟶ B)
    (hf : (SSet.ι₀ (X := A) ▷ T) ≫ f = fst A T)
    (hg : (SSet.ι₁ (X := B) ▷ T) ≫ g = fst B T) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B ▷ T) ≫ fatJoinTransformFamily f g hf hg = fst B T ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr A B :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_descTensorRight _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

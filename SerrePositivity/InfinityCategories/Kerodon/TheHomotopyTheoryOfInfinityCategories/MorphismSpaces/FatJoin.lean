module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinTensorRight
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：区間の両端を射影で潰した fat join の構成。
方針：A×Δ[1]×B の零端を A、一端を B に二つの pushout で貼る。
規約：既存の直接定義の join は変更しない。
使われ方：Kerodon Notation 4.6.2.3（Tag 01HR）、Example 4.6.6.8（Tag 04J5） の slice 比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：fat join の零端を A へ潰した最初の pushout。
方針：区間の零端と第一射影を貼る。
規約：円柱は (A×Δ[1])×B の順。
使われ方：Kerodon Notation 4.6.2.3（Tag 01HR） の fat join の構成。 -/
@[kerodon 01HR]
noncomputable def fatJoinStage (A B : SSet.{u}) : SSet.{u} :=
  pushout (SSet.ι₀ (X := A) ▷ B) (fst A B)

/-- 概要：最初の pushout への区間の一端の射。
方針：区間の一端を含めて円柱の pushout 包含で写す。
規約：始域は A×B。
使われ方：Kerodon Notation 4.6.2.3（Tag 01HR） の第二の貼り合わせ。 -/
noncomputable def fatJoinStageEnd (A B : SSet.{u}) : A ⊗ B ⟶ fatJoinStage A B :=
  (SSet.ι₁ (X := A) ▷ B) ≫ pushout.inl _ _

/-- 概要：二つの単体集合の fat join。
方針：最初の pushout の一端を B へ第二射影で潰す。
規約：直接定義の join との比較のための補助模型。
使われ方：Kerodon Notation 4.6.2.3（Tag 01HR）、§4.6.6（Tag 04HY）。 -/
@[kerodon 01HR]
noncomputable def fatJoin (A B : SSet.{u}) : SSet.{u} :=
  pushout (fatJoinStageEnd A B) (snd A B)

/-- 概要：円柱から fat join への標準射。
方針：二段の pushout の左包含を合成する。
規約：円柱の因子の順序は (A×Δ[1])×B。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較とホモトピーの構成。 -/
noncomputable def fatJoinCylinder (A B : SSet.{u}) :
    (A ⊗ (Δ[1] : SSet.{u})) ⊗ B ⟶ fatJoin A B :=
  pushout.inl (SSet.ι₀ (X := A) ▷ B) (fst A B) ≫ pushout.inl _ _

/-- 概要：fat join の左包含。
方針：最初の pushout の右包含と二段目の左包含を合成する。
規約：零端に対応する。
使われ方：Kerodon §4.6.2（Tag 01HM） の左因子の固定。 -/
noncomputable def fatJoinInl (A B : SSet.{u}) : A ⟶ fatJoin A B :=
  pushout.inr (SSet.ι₀ (X := A) ▷ B) (fst A B) ≫ pushout.inl _ _

/-- 概要：fat join の右包含。
方針：第二の pushout の右包含を取る。
規約：一端に対応する。
使われ方：Kerodon §4.6.2（Tag 01HM） の右因子の固定。 -/
noncomputable def fatJoinInr (A B : SSet.{u}) : B ⟶ fatJoin A B :=
  pushout.inr _ _

/-- 概要：円柱の零端は左射影後の左包含に一致する。
方針：最初の pushout の可換性を使う。
規約：円柱の左端の全ての B 成分を忘れる。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join の普遍性。 -/
lemma fatJoinCylinder_zero (A B : SSet.{u}) :
    (SSet.ι₀ (X := A) ▷ B) ≫ fatJoinCylinder A B = fst A B ≫ fatJoinInl A B := by
  unfold fatJoinCylinder fatJoinInl
  rw [← Category.assoc, pushout.condition, Category.assoc]

/-- 概要：円柱の一端は右射影後の右包含に一致する。
方針：第二の pushout の可換性を使う。
規約：円柱の右端の全ての A 成分を忘れる。
使われ方：Kerodon §4.6.2（Tag 01HM） の fat join の普遍性。 -/
lemma fatJoinCylinder_one (A B : SSet.{u}) :
    (SSet.ι₁ (X := A) ▷ B) ≫ fatJoinCylinder A B = snd A B ≫ fatJoinInr A B := by
  change (SSet.ι₁ (X := A) ▷ B) ≫
      pushout.inl (SSet.ι₀ (X := A) ▷ B) (fst A B) ≫ pushout.inl _ _ = _
  rw [← Category.assoc]
  exact pushout.condition

/-- 概要：円柱と両因子上の整合する射から fat join 上の射を作る。
方針：二つの pushout の普遍性を順に使う。
規約：両端の整合条件は射の厳密な等式。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射とホモトピーの貼り合わせ。 -/
noncomputable def fatJoinDesc {A B X : SSet.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (H : (A ⊗ (Δ[1] : SSet.{u})) ⊗ B ⟶ X)
    (h₀ : (SSet.ι₀ (X := A) ▷ B) ≫ H = fst A B ≫ f)
    (h₁ : (SSet.ι₁ (X := A) ▷ B) ≫ H = snd A B ≫ g) : fatJoin A B ⟶ X :=
  pushout.desc (pushout.desc H f h₀) g (by
    change ((SSet.ι₁ (X := A) ▷ B) ≫ pushout.inl _ _) ≫ pushout.desc H f h₀ = _
    rw [Category.assoc, pushout.inl_desc]
    exact h₁)

/-- 概要：fat join の貼り合わせは円柱上で指定された射に一致する。
方針：二段の pushout の左包含の計算を使う。
規約：整合条件は貼り合わせの定義と同じもの。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の計算。 -/
lemma fatJoinCylinder_desc {A B X : SSet.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (H : (A ⊗ (Δ[1] : SSet.{u})) ⊗ B ⟶ X)
    (h₀ : (SSet.ι₀ (X := A) ▷ B) ≫ H = fst A B ≫ f)
    (h₁ : (SSet.ι₁ (X := A) ▷ B) ≫ H = snd A B ≫ g) :
    fatJoinCylinder A B ≫ fatJoinDesc f g H h₀ h₁ = H := by
  unfold fatJoinCylinder fatJoinDesc
  rw [Category.assoc, pushout.inl_desc, pushout.inl_desc]

/-- 概要：fat join の貼り合わせは左因子上で指定された射に一致する。
方針：二段の pushout の包含の計算を使う。
規約：零端の射を回収する。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の左包含。 -/
lemma fatJoinInl_desc {A B X : SSet.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (H : (A ⊗ (Δ[1] : SSet.{u})) ⊗ B ⟶ X)
    (h₀ : (SSet.ι₀ (X := A) ▷ B) ≫ H = fst A B ≫ f)
    (h₁ : (SSet.ι₁ (X := A) ▷ B) ≫ H = snd A B ≫ g) :
    fatJoinInl A B ≫ fatJoinDesc f g H h₀ h₁ = f := by
  unfold fatJoinInl fatJoinDesc
  rw [Category.assoc, pushout.inl_desc, pushout.inr_desc]

/-- 概要：fat join の貼り合わせは右因子上で指定された射に一致する。
方針：第二の pushout の右包含の計算を使う。
規約：一端の射を回収する。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較射の右包含。 -/
lemma fatJoinInr_desc {A B X : SSet.{u}} (f : A ⟶ X) (g : B ⟶ X)
    (H : (A ⊗ (Δ[1] : SSet.{u})) ⊗ B ⟶ X)
    (h₀ : (SSet.ι₀ (X := A) ▷ B) ≫ H = fst A B ≫ f)
    (h₁ : (SSet.ι₁ (X := A) ▷ B) ≫ H = snd A B ≫ g) :
    fatJoinInr A B ≫ fatJoinDesc f g H h₀ h₁ = g :=
  pushout.inr_desc _ _ _

/-- 概要：fat join 上の二射は円柱と両因子上で一致すれば等しい。
方針：二つの pushout の外延性を使う。
規約：両端の包含も指定する。
使われ方：Kerodon §4.6.2（Tag 01HM） の比較とホモトピーの等式。 -/
lemma fatJoin_hom_ext {A B X : SSet.{u}} {f g : fatJoin A B ⟶ X}
    (hH : fatJoinCylinder A B ≫ f = fatJoinCylinder A B ≫ g)
    (hf : fatJoinInl A B ≫ f = fatJoinInl A B ≫ g)
    (hg : fatJoinInr A B ≫ f = fatJoinInr A B ≫ g) : f = g := by
  apply pushout.hom_ext
  · apply pushout.hom_ext
    · simpa only [fatJoinCylinder, Category.assoc] using hH
    · simpa only [fatJoinInl, Category.assoc] using hf
  · exact hg

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.2.1.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin
attribute [cite HTT "4.2.1.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinStage

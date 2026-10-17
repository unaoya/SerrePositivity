module
public import SerrePositivity.DifferentialGraded.Morita.AdjunctionBrownSeed

/-! # 表現対象の近似における生成元の全関係

## 概要
指定した射L(X)→Yについて、生成元から来てその像が零になる射を一つの余積からの射にまとめる。

## 方針
局所小性で関係の添字をuへ縮小する。指定余積の保存からL像が零になることを証明する。

## 規約と注意
随伴の存在は仮定しない。関係を消すconeは次の段階で構成する。

## 使われ方
U16aの一般右随伴の表現対象を構成する、初期被覆からの後続段階の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  {X : DerivedModuleCategory A D} {Y : DerivedModuleCategory A E} (r : L.obj X ⟶ Y)

/-- 生成元からXに来て、rの下で零になる全ての射。 -/
def brownRelationRawIndex :=
  Σ p : D × ℤ, {f : moduleCompactGenerators A D p ⟶ X // L.map f ≫ r = 0}

/-- 既存の局所小性により、全関係の添字もu-small。 -/
instance brownRelationRawIndexSmall : Small.{u} (brownRelationRawIndex A D E L r) := by
  dsimp only [brownRelationRawIndex]
  infer_instance

/-- u-smallな関係の実際の添字。 -/
abbrev brownRelationIndex := Shrink.{u} (brownRelationRawIndex A D E L r)

/-- 各関係の源となる生成元。 -/
def brownRelationFamily (i : brownRelationIndex A D E L r) : DerivedModuleCategory A D :=
  moduleCompactGenerators A D (((equivShrink (brownRelationRawIndex A D E L r)).symm i).1)

/-- 各関係をXへの射として取り出す。 -/
def brownRelationArrow (i : brownRelationIndex A D E L r) :
    brownRelationFamily A D E L r i ⟶ X :=
  ((equivShrink (brownRelationRawIndex A D E L r)).symm i).2.val

/-- 各関係のL像とrの合成は零。 -/
lemma brownRelationArrow_condition (i : brownRelationIndex A D E L r) :
    L.map (brownRelationArrow A D E L r i) ≫ r = 0 :=
  ((equivShrink (brownRelationRawIndex A D E L r)).symm i).2.property

/-- 全関係の源は生成元のu-small余積。 -/
def brownRelationObject : DerivedModuleCategory A D := ∐ brownRelationFamily A D E L r

/-- 全関係をまとめたXへの射。 -/
def brownRelationMap : brownRelationObject A D E L r ⟶ X :=
  Sigma.desc (brownRelationArrow A D E L r)

/-- 関係の包含からの合成は元の関係を計算する。 -/
lemma brownRelationMap_ι (i : brownRelationIndex A D E L r) :
    Sigma.ι (brownRelationFamily A D E L r) i ≫ brownRelationMap A D E L r =
      brownRelationArrow A D E L r i := Sigma.ι_comp_desc _ _

/-- 関係余積の保存により、全関係の射のL像もrで零になる。 -/
lemma brownRelationMap_image_zero
    [PreservesColimit (Discrete.functor (brownRelationFamily A D E L r)) L] :
    L.map (brownRelationMap A D E L r) ≫ r = 0 := by
  apply (isColimitOfHasCoproductOfPreservesColimit L
    (brownRelationFamily A D E L r)).hom_ext
  rintro ⟨i⟩
  change L.map (Sigma.ι (brownRelationFamily A D E L r) i) ≫
    (L.map (brownRelationMap A D E L r) ≫ r) =
    L.map (Sigma.ι (brownRelationFamily A D E L r) i) ≫ 0
  rw [← Category.assoc, ← Functor.map_comp, brownRelationMap_ι, comp_zero]
  exact brownRelationArrow_condition A D E L r i

/-- 全関係の射を殺すXからの射は、rに関する生成元からの任意の関係を殺す。 -/
lemma brownRelationMap_kills {Z : DerivedModuleCategory A D} (g : X ⟶ Z)
    (hg : brownRelationMap A D E L r ≫ g = 0) (p : D × ℤ)
    (f : moduleCompactGenerators A D p ⟶ X) (hf : L.map f ≫ r = 0) : f ≫ g = 0 := by
  let T := brownRelationRawIndex A D E L r
  let good : T → Prop := fun t => t.2.val ≫ g = 0
  obtain ⟨i, hi⟩ := (equivShrink T).symm.surjective (⟨p, ⟨f, hf⟩⟩ : T)
  have h : brownRelationArrow A D E L r i ≫ g = 0 := by
    rw [← brownRelationMap_ι A D E L r i, Category.assoc, hg, comp_zero]
  change good ((equivShrink T).symm i) at h
  rw [hi] at h
  exact h

end SerrePositivity.DifferentialGraded.Morita

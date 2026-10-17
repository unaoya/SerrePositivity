module
public import SerrePositivity.DifferentialGraded.Perfect.Generators
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # 導来右随伴の表現対象を構成する初期生成元被覆

## 概要
余積を保つ指定関手Lと終域対象Yに対し、全ての生成元からのL像の射を初期対象で表す。

## 方針
局所小性で全射の添字をuへ縮小し、代表加群の整数shiftの余積と比較同型を使う。

## 規約と注意
指定した余積の保存を明示する。随伴の存在や表現可能性は仮定しない。
これは初期被覆であり、関係を消す段階と極限での表現可能性の証明は後続の仕事。

## 使われ方
U16aの一般kernelの右随伴を、compact生成元から引用なしに構成するための初期段階。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory Limits
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (L : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
  (Y : DerivedModuleCategory A E)

/-- 全てのshiftした代表加群のL像からYへの射。 -/
def brownSeedRawIndex := Σ p : D × ℤ, L.obj (moduleCompactGenerators A D p) ⟶ Y

/-- 生成元の添字と局所小性から、全射の添字は係数・Hom宇宙uでsmall。 -/
instance brownSeedRawIndexSmall : Small.{u} (brownSeedRawIndex A D E L Y) := by
  dsimp only [brownSeedRawIndex]
  infer_instance

/-- u-smallな実際の余積添字。 -/
abbrev brownSeedIndex := Shrink.{u} (brownSeedRawIndex A D E L Y)

/-- 初期被覆に使う生成元の族。 -/
def brownSeedFamily (i : brownSeedIndex A D E L Y) : DerivedModuleCategory A D :=
  moduleCompactGenerators A D (((equivShrink (brownSeedRawIndex A D E L Y)).symm i).1)

/-- 各生成元のL像からYへの、添字そのものが指定する射。 -/
def brownSeedArrow (i : brownSeedIndex A D E L Y) :
    L.obj (brownSeedFamily A D E L Y i) ⟶ Y :=
  ((equivShrink (brownSeedRawIndex A D E L Y)).symm i).2

/-- 初期被覆の源はu-smallな生成元余積。 -/
def brownSeed : DerivedModuleCategory A D := ∐ brownSeedFamily A D E L Y

/-- 初期被覆のL像からYへの射。余積比較を反転して構成する。 -/
def brownSeedMap [PreservesColimit (Discrete.functor (brownSeedFamily A D E L Y)) L] :
    L.obj (brownSeed A D E L Y) ⟶ Y :=
  (PreservesCoproduct.iso L (brownSeedFamily A D E L Y)).hom ≫
    Sigma.desc (brownSeedArrow A D E L Y)

variable [PreservesColimit (Discrete.functor (brownSeedFamily A D E L Y)) L]

/-- 初期被覆の各成分の像は、指定した元の射そのもの。 -/
lemma brownSeedMap_ι (i : brownSeedIndex A D E L Y) :
    L.map (Sigma.ι (brownSeedFamily A D E L Y) i) ≫ brownSeedMap A D E L Y =
      brownSeedArrow A D E L Y i := by
  dsimp only [brownSeedMap]
  rw [← ι_comp_sigmaComparison L (brownSeedFamily A D E L Y) i,
    ← PreservesCoproduct.inv_hom L (brownSeedFamily A D E L Y), Category.assoc,
    Iso.inv_hom_id_assoc, Sigma.ι_comp_desc]

/-- 各compact生成元のL像からの任意の射は、初期被覆のL像を経由する。 -/
lemma brownSeedMap_generator_surjective (p : D × ℤ)
    (f : L.obj (moduleCompactGenerators A D p) ⟶ Y) :
    ∃ g : moduleCompactGenerators A D p ⟶ brownSeed A D E L Y,
      L.map g ≫ brownSeedMap A D E L Y = f := by
  let T := brownSeedRawIndex A D E L Y
  let good : T → Prop := fun r =>
    ∃ g : moduleCompactGenerators A D r.1 ⟶ brownSeed A D E L Y,
      L.map g ≫ brownSeedMap A D E L Y = r.2
  obtain ⟨i, hi⟩ := (equivShrink T).symm.surjective (⟨p, f⟩ : T)
  have h : good ((equivShrink T).symm i) :=
    ⟨Sigma.ι (brownSeedFamily A D E L Y) i, brownSeedMap_ι A D E L Y i⟩
  rw [hi] at h
  exact h

end SerrePositivity.DifferentialGraded.Morita

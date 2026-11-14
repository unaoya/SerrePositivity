module


public meta import SerrePositivity.Util.Citation
public import Mathlib.Algebra.Group.WithOne.Defs
public import Mathlib.AlgebraicTopology.Quasicategory.Nerve
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：coherent な冪等図式とその強い分裂の小さい添字を構成する。
方針：二元冪等モノイドの一対象圏と、その二つの形式的像の圏の nerve を使う。
規約：Karoubi は添字圏の構成だけに使用し、一般の ∞ 圏の完備化は後で証明する。
使われ方：HTT 4.4.5 の Idem と Idem⁺、F2N-4 の coherent 分裂。

対応節は Kerodon 8.5（Tag 03Y9）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
attribute [local instance] uliftCategory
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-- 恒等と一つの非恒等冪等元を持つ一対象圏。 -/
@[kerodon 03ZN]
abbrev WalkingIdem := ULift.{u} (SingleObj (WithOne PUnit.{u + 1}))

/-- 両宇宙を同じ小さい宇宙に揃えた添字圏の構造。 -/
instance walkingIdemCategory : SmallCategory WalkingIdem.{u} := inferInstance

/-- 元の一対象。 -/
def walkingObject : WalkingIdem.{u} := ⟨SingleObj.star _⟩

/-- 元の非恒等冪等元。 -/
def walkingIdempotent : walkingObject.{u} ⟶ walkingObject.{u} :=
  show WithOne PUnit.{u + 1} from ↑PUnit.unit

/-- 指定した元の射は冪等。 -/
@[kerodon 03ZN]
lemma walkingIdempotent_idem :
    walkingIdempotent.{u} ≫ walkingIdempotent.{u} = walkingIdempotent.{u} := rfl

/-- 指定した元の冪等元は恒等射ではない。 -/
lemma walkingIdempotent_ne_id : walkingIdempotent.{u} ≠ 𝟙 walkingObject := by
  exact WithOne.coe_ne_one

/-- 強い分裂の添字圏。元の冪等元と恒等の二つの形式的像を持つ。 -/
@[kerodon 03YB]
abbrev WalkingSplit := CategoryTheory.Idempotents.Karoubi WalkingIdem.{u}

/-- 元の冪等図式から強い分裂図式への包含。 -/
def walkingInclusion : WalkingIdem.{u} ⥤ WalkingSplit.{u} :=
  CategoryTheory.Idempotents.toKaroubi _

/-- 強い分裂の元の非分裂対象。 -/
def walkingSource : WalkingSplit.{u} := walkingInclusion.obj walkingObject

/-- 元の冪等元の像としての分裂対象。 -/
def walkingImage : WalkingSplit.{u} := ⟨walkingObject, walkingIdempotent, walkingIdempotent_idem⟩

/-- 分裂対象から元の対象への包含。 -/
def walkingSection : walkingImage.{u} ⟶ walkingSource.{u} :=
  CategoryTheory.Idempotents.Karoubi.decompId_i walkingImage

/-- 元の対象から分裂対象への射影。 -/
def walkingRetraction : walkingSource.{u} ⟶ walkingImage.{u} :=
  CategoryTheory.Idempotents.Karoubi.decompId_p walkingImage

/-- 分裂の合成は同じ分裂対象の恒等。 -/
@[kerodon 03YB]
lemma walkingSection_retraction :
    walkingSection.{u} ≫ walkingRetraction.{u} = 𝟙 walkingImage :=
  (CategoryTheory.Idempotents.Karoubi.decompId walkingImage).symm

/-- 逆順の合成は元の非恒等冪等元の像。 -/
lemma walkingRetraction_section :
    walkingRetraction.{u} ≫ walkingSection.{u} = walkingInclusion.map walkingIdempotent :=
  (CategoryTheory.Idempotents.Karoubi.decomp_p walkingImage).symm

/-- coherent 冪等図式の元の小さい単体集合。 -/
@[kerodon 03ZT]
def IdemShape : SSet.{u} := nerve WalkingIdem.{u}

/-- coherent な強い分裂の元の小さい単体集合。 -/
def SplitShape : SSet.{u} := nerve WalkingSplit.{u}

/-- 冪等図式の添字は元の通常の圏の nerve として quasicategory。 -/
instance idemShape_quasicategory : Quasicategory IdemShape.{u} :=
  inferInstanceAs (Quasicategory (nerve WalkingIdem.{u}))

/-- 強い分裂の添字も元の通常の圏の nerve として quasicategory。 -/
instance splitShape_quasicategory : Quasicategory SplitShape.{u} :=
  inferInstanceAs (Quasicategory (nerve WalkingSplit.{u}))

/-- 元の coherent 冪等図式を強い分裂へ制限するための包含。 -/
def idemInclusion : IdemShape.{u} ⟶ SplitShape.{u} := nerveMap walkingInclusion.{u}

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.4.5.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape
attribute [cite HTT "4.4.5.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.SplitShape
attribute [cite HTT "4.4.5.3" (partial := component) "仮定：HTT の Idem（一致）。結論：恒等元と非恒等冪等元を持つ二元モノイドの一対象圏の神経として定義する（一致する成分。各次元の非退化単体の個数とこの性質による一意性は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IdemShape
attribute [cite HTT "4.4.5.3" (partial := component) "仮定：HTT の Idem（一致）。結論：恒等元と非恒等冪等元を持つ二元モノイドの一対象圏の神経として定義する（一致する成分。各次元の非退化単体の個数とこの性質による一意性は含まない）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.WalkingIdem

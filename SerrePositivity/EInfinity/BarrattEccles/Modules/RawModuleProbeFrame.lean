module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorFrame
public import SerrePositivity.EInfinity.Modules.DGResolutionAdjunction

/-!
# 元の半自由 probe 全族と同じ正規化テンソル frame

概要：M10 の frame 比較へ、元の半自由 dg 部分圏の全包含をパラメータにする。
方針：既存の閉零包含と全テンソル族を合成し、同じ augmentation を前合成する。
規約：HA §1.3.4、対象ごとの frame 選択に置き換えない。
使われ方：N01 の選択済み frame と元の dg Hom の全自然比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A]

/-- 概要：元の半自由 dg 部分圏の閉零圏を probe のパラメータにする。
方針：既存の同じ dg 部分圏を使う。
規約：HA §1.3.4、全閉零射。使われ方：二変数の frame 比較の始域。 -/
abbrev strictRawModuleProbeCategory (X : (operad A).Algebra) : Type (u + 1) :=
  ClosedCategory A (SemifreeDGModules A (dgAlgebraCategory A ((assocForget A).obj X)))

/-- 概要：元の全ての半自由加群を同じ通常加群へ含める全関手。
方針：既存の dg 全包含を閉零圏へ送る。
規約：HA §1.3.4、同じ Hom を保つ。使われ方：共通 augmentation の底。 -/
def strictRawModuleProbeFunctor (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ strictRawModuleCategory A X :=
  (semifreeInclusion A (dgAlgebraCategory A ((assocForget A).obj X))).onClosed

/-- 概要：同じ probe の値は元の意味で半自由。
方針：既存の dg 部分圏の性質を回収する。
規約：HA §1.3.4、別の置換にしない。使われ方：同じ frame 条件。 -/
lemma strictRawModuleProbeFunctor_semifree (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    moduleSemifree A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleProbeFunctor A X).obj P) :=
  (ForgetEnrichment.to (Complex A) P).property

/-- 概要：同じ半自由 probe は N01 の実モデルで cofibrant。
方針：検証済みの元の半自由対象の照合を使う。
規約：HA §1.3.4、実モデル。使われ方：選択済み frame の底。 -/
lemma strictRawModuleProbeFunctor_cofibrant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    let := strictRawModuleModelCategory A X
    IsCofibrant ((strictRawModuleProbeFunctor A X).obj P) :=
  strictRawModuleModelCategory_semifreeCofibrant A X (ForgetEnrichment.to (Complex A) P)

/-- 概要：同じ半自由全族の正規化単体テンソル frame。
方針：元の包含の後に同じ全テンソル族を合成する。
規約：HA §1.3.4、全 probe 射。使われ方：選択済み frame との実比較。 -/
def strictRawModuleProbeTensorFrame (X : (operad A).Algebra) :
    strictRawModuleProbeCategory A X ⥤ (SimplexCategory ⥤ strictRawModuleCategory A X) :=
  strictRawModuleProbeFunctor A X ⋙
    moduleTensorSimplicesFunctor A (dgAlgebraCategory A ((assocForget A).obj X))

/-- 概要：同じ全 frame から元の probe への全自然 augmentation。
方針：同じ AW 余単位の全族を元の包含で前合成する。
規約：HA §1.3.4、同じ底。使われ方：共通 frame の実 pullback。 -/
def strictRawModuleProbeTensorAugmentation (X : (operad A).Algebra) :
    strictRawModuleProbeTensorFrame A X ⟶
      strictRawModuleProbeFunctor A X ⋙ Functor.const SimplexCategory :=
  Functor.whiskerLeft (strictRawModuleProbeFunctor A X)
    (moduleTensorSimplicesAugmentationFamily A (dgAlgebraCategory A ((assocForget A).obj X)))

/-- 概要：同じ probe 全族の各 frame は実 Reedy cofibrant。
方針：同じ probe の半自由性を検証済みの frame 条件へ渡す。
規約：HA §1.3.4、実モデル。使われ方：固定 Quillen 類の frame 不変性。 -/
lemma strictRawModuleProbeTensorFrame_cofibrant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) :
    let := strictRawModuleModelCategory A X
    reedyLeft simplex (cofibrations (strictRawModuleCategory A X))
      (initial.to ((strictRawModuleProbeTensorFrame A X).obj P)) :=
  strictRawModuleTensorFrame_reedyCofibrant A X _ (strictRawModuleProbeFunctor_semifree A X P)

/-- 概要：同じ全 augmentation の各成分は実モデルの元の弱同値。
方針：検証済みの同じ AW 余単位の弱同値性を使う。
規約：HA §1.3.4、同じ射。使われ方：共通 frame の左比較。 -/
lemma strictRawModuleProbeTensorAugmentation_weak (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) (n : SimplexCategory) :
    let := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((strictRawModuleProbeTensorAugmentation A X).app P).app n) := by
  dsimp only
  exact (strictRawModuleModelCategory_weakEquivalences A X).symm ▸
    strictRawModuleTensorFrame_augmentation_weak A X _
      (strictRawModuleProbeFunctor_semifree A X P) n

/-- 概要：同じ probe frame は全ての面・退化で元の弱同値。
方針：検証済みの同じ半自由 frame の定数性を使う。
規約：HA §1.3.4、全作用素。使われ方：共通 frame の右比較。 -/
lemma strictRawModuleProbeTensorFrame_homotopicallyConstant (X : (operad A).Algebra)
    (P : strictRawModuleProbeCategory A X) {n m : SimplexCategory} (f : n ⟶ m) :
    let := strictRawModuleModelCategory A X
    weakEquivalences (strictRawModuleCategory A X)
      (((strictRawModuleProbeTensorFrame A X).obj P).map f) :=
  strictRawModuleTensorFrame_homotopicallyConstant A X _
    (strictRawModuleProbeFunctor_semifree A X P) f

end SerrePositivity.EInfinity.BarrattEccles

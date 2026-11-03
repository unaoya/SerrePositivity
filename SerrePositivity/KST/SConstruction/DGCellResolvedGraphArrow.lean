module
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGFunctorGraphParameter
public import SerrePositivity.DifferentialGraded.Resolution.Cell
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Derived.BimoduleTensor
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement

/-!
概要：同じ cell source 上に元全 Hom 自然な関手 graph と比較射の解像度を保持する。
方針：両脚を同じ増大で制限し、既存の semifree bimodule 解像度と実比較持ち上げを使う。
規約：各右制限の射影的 perfect 性は別条件であり、ここで仮定充足と数えない。
使われ方：固定 cell gluing 上の右軸から恒等への実 dg 比較の接続準備と D 供給型。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) [DGCategory R B] [Small.{u} B]
local notation "P" => DGCategoryCellResolution.Source R B
local notation "α" => DGCategoryCellResolution.augmentation R B

/-- 概要：元関手の graph を同じ cell 増大の両脚で制限した実 bimodule。
方針：元の全 Hom を持つ graph と同じ両脚制限を使う。
規約：同じ増大を保持。使われ方：元 gluing の右軸と恒等の二 graph。 -/
def dgCellRestrictedGraph (F : DGFunctor R B B) : BimoduleCategory R (P) (P) :=
  (BimoduleCategory.pairedRestrictionFunctor R B B (P) (P) (α) (α)).obj
    (BimoduleCategory.of R B B (functorGraph R B B F))

/-- 概要：元全 dg 比較を同じ制限 graph 間の実 bimodule 射にする。
方針：元の単位パラメータ付き graph 作用と既存の閉射対応を使う。
規約：元全次数自然性を保持。使われ方：同じ cell source 上の実右軸比較。 -/
def dgCellRestrictedGraphMap (F G : DGFunctor R B B)
    (τ : DGFunctorParamTrans R B B (𝟙_ (Complex R)) F G) :
    dgCellRestrictedGraph R B F ⟶ dgCellRestrictedGraph R B G :=
  (BimoduleCategory.pairedRestrictionFunctor R B B (P) (P) (α) (α)).map
    ((BimoduleCategory.homEquiv R B B
      (BimoduleCategory.of R B B (functorGraph R B B F))
      (BimoduleCategory.of R B B (functorGraph R B B G))).symm
        (dgFunctorGraphParameter R B B τ))

/-- 概要：同じ制限 graph の指定 semifree bimodule 解像度。
方針：既存の標準解像度を同じ元 graph に適用する。
規約：右制限の射影性はまだ主張しない。使われ方：実比較の解像度側の二対象。 -/
def dgCellResolvedGraphResolution (F : DGFunctor R B B) :
    BimoduleSemifreeResolution R (P) (P) (dgCellRestrictedGraph R B F) :=
  bimoduleCanonicalSemifreeResolution R (P) (P) (dgCellRestrictedGraph R B F)

/-- 概要：元比較を同じ二解像度間の全 Hom 自然な実 bimodule 射として保持する。
方針：既存の同じ解像度間の比較持ち上げを使う。
規約：増大との可換性は導来像で保持する。使われ方：同じ実 dg 比較の候補射。 -/
def dgCellResolvedGraphMap (F G : DGFunctor R B B)
    (τ : DGFunctorParamTrans R B B (𝟙_ (Complex R)) F G) :
    (dgCellResolvedGraphResolution R B F).obj ⟶ (dgCellResolvedGraphResolution R B G).obj :=
  (dgCellResolvedGraphResolution R B F).lift R (P) (P)
    (dgCellResolvedGraphResolution R B G) (dgCellRestrictedGraphMap R B F G τ)

/-- 概要：同じ実解像度比較の増大 square は主導来 bimodule 圏で可換。
方針：既存持ち上げの同じ増大比較をそのまま適用する。
規約：厳密な増大等号や native 全比較で代用しない。使われ方：元比較の回収の入力。 -/
lemma dgCellResolvedGraphMap_fac (F G : DGFunctor R B B)
    (τ : DGFunctorParamTrans R B B (𝟙_ (Complex R)) F G) :
    (bimoduleToDerived R (P) (P)).map (dgCellResolvedGraphMap R B F G τ) ≫
        (bimoduleToDerived R (P) (P)).map (dgCellResolvedGraphResolution R B G).π =
      (bimoduleToDerived R (P) (P)).map (dgCellResolvedGraphResolution R B F).π ≫
        (bimoduleToDerived R (P) (P)).map (dgCellRestrictedGraphMap R B F G τ) :=
  (dgCellResolvedGraphResolution R B F).lift_fac R (P) (P)
    (dgCellResolvedGraphResolution R B G) (dgCellRestrictedGraphMap R B F G τ)

/-- 概要：実解像度 graph の各右制限が射影的 perfect であるという未供給条件。
方針：同じ選んだ graph 解像度と全 cell 対象に対する証拠を固定する。
規約：条件の存在は未証明。使われ方：D 向けの正確な供給型と実 Perf 関手への制限。 -/
def DGCellResolvedGraphPerfectCondition (F : DGFunctor R B B) : Prop :=
  ∀ x : P, modulePerfectProjectiveOver R (P) Set.univ
    ((BimoduleCategory.underlying R (P) (P) (dgCellResolvedGraphResolution R B F).obj).rightAt x)
end SerrePositivity.KST.SConstruction

module
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphPerfect
public import SerrePositivity.KST.SConstruction.DGBimodulePerfectFunctor
public import SerrePositivity.KST.SConstruction.DGFunctorClosedComparison

/-!
概要：同じ graph 解像度と実比較を各右制限の射影性だけから実 Perf dg 関手へ接続する。
方針：証明済み Perf 性と射影性を束ね、同じ始域・全 Hom・実 bimodule 射を保持する。
規約：射影性の供給は明示入力。実 LT 長方形の完成と数えない。
使われ方：D の追加証拠を元 cell source 上の右軸比較へ差し替える接続口。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (B : Type v) [DGCategory R B] [Small.{u} B]
local notation "P" => DGCategoryCellResolution.Source R B

/-- 概要：同じ解像度 graph を実右加群に値を持つ全 dg 関手として読む。
方針：元 bimodule の左作用をそのまま使う。
規約：全対象・全 Hom を保持。使われ方：固定 cell source の元実関手。 -/
def dgCellResolvedGraphModuleFunctor (F : DGFunctor R B B) :
    DGFunctor R (P) (RightModule R (P)) :=
  BimoduleCategory.underlying R (P) (P) (dgCellResolvedGraphResolution R B F).obj

/-- 概要：同じ実右制限の射影性だけで元 cell source からの Perf dg 関手を構成する。
方針：証明済み Perf 性と指定射影性を同じ対象に付ける。
規約：始域と元対象は不変。使われ方：D の証拠を全 dg 関手へ接続する。 -/
def dgCellResolvedGraphPerfectFunctor (F : DGFunctor R B B)
    (h : DGCellResolvedGraphProjectiveCondition R B F) :
    DGFunctor R (P) (PerfectDGModule R (P)) :=
  dgBimodulePerfectFunctor R (P) (P) (dgCellResolvedGraphResolution R B F).obj
    (dgCellResolvedGraphPerfectCondition_of_projective R B F h)

/-- 概要：同じ Perf 関手の包含後は元解像度 graph の全作用。
方針：実対象を保つ制限の回収式を使う。
規約：全 dg 関手の等号。使われ方：元 graph 比較との厳密照合。 -/
lemma dgCellResolvedGraphPerfectFunctor_inclusion (F : DGFunctor R B B)
    (h : DGCellResolvedGraphProjectiveCondition R B F) :
    (dgCellResolvedGraphPerfectFunctor R B F h).comp
      (perfectDGModuleInclusion R (P) Set.univ) = dgCellResolvedGraphModuleFunctor R B F :=
  dgBimodulePerfectFunctor_inclusion R (P) (P) (dgCellResolvedGraphResolution R B F).obj
    (dgCellResolvedGraphPerfectCondition_of_projective R B F h)

variable (F G : DGFunctor R B B)
  (hF : DGCellResolvedGraphProjectiveCondition R B F)
  (hG : DGCellResolvedGraphProjectiveCondition R B G)
  (τ : DGFunctorParamTrans R B B (𝟙_ (Complex R)) F G)

/-- 概要：同じ実解像度比較を元 cell source 上の実 Perf 閉射族にする。
方針：元全 Hom 自然な bimodule 射を同じ perfect 対象間へ制限する。
規約：元射を保持。使われ方：右軸から恒等への全比較の実成分。 -/
def dgCellResolvedGraphPerfectMap (x : P) :
    ForgetEnrichment.of (Complex R) ((dgCellResolvedGraphPerfectFunctor R B F hF).obj x) ⟶
      ForgetEnrichment.of (Complex R) ((dgCellResolvedGraphPerfectFunctor R B G hG).obj x) :=
  dgBimodulePerfectMap R (P) (P)
    (dgCellResolvedGraphResolution R B F).obj (dgCellResolvedGraphResolution R B G).obj
    (dgCellResolvedGraphPerfectCondition_of_projective R B F hF)
    (dgCellResolvedGraphPerfectCondition_of_projective R B G hG)
    (dgCellResolvedGraphMap R B F G τ) x

/-- 概要：同じ実 Perf 射族は元 cell source の全 Hom に関して自然。
方針：元 bimodule 射の全自然性を同じ perfect 制限へ移す。
規約：全次数と元射を保持。使われ方：実 dg 自然変換への束ね。 -/
lemma dgCellResolvedGraphPerfectMap_hom_naturality (x y : P) :
    (dgCellResolvedGraphPerfectFunctor R B F hF).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgCellResolvedGraphPerfectFunctor R B F hF).obj x))
        (dgCellResolvedGraphPerfectMap R B F G hF hG τ y) =
    (dgCellResolvedGraphPerfectFunctor R B G hG).map x y ≫
      eHomWhiskerRight (Complex R) (dgCellResolvedGraphPerfectMap R B F G hF hG τ x)
        (ForgetEnrichment.of (Complex R) ((dgCellResolvedGraphPerfectFunctor R B G hG).obj y)) :=
  dgBimodulePerfectMap_hom_naturality R (P) (P)
    (dgCellResolvedGraphResolution R B F).obj (dgCellResolvedGraphResolution R B G).obj
    (dgCellResolvedGraphPerfectCondition_of_projective R B F hF)
    (dgCellResolvedGraphPerfectCondition_of_projective R B G hG)
    (dgCellResolvedGraphMap R B F G τ) x y

/-- 概要：同じ実 Perf 関手と元比較を単位パラメータの全 dg 自然変換に束ねる。
方針：元閉射族と全 Hom 自然性を使う。
規約：右制限の射影性だけに条件付き。使われ方：同じ cell gluing の実 Hom gluing 比較。 -/
def dgCellResolvedGraphPerfectComparison :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R)))
      (dgCellResolvedGraphPerfectFunctor R B F hF) (dgCellResolvedGraphPerfectFunctor R B G hG) :=
  dgFunctorClosedComparison R _ _ (dgCellResolvedGraphPerfectMap R B F G hF hG τ)
    (dgCellResolvedGraphPerfectMap_hom_naturality R B F G hF hG τ)
end SerrePositivity.KST.SConstruction

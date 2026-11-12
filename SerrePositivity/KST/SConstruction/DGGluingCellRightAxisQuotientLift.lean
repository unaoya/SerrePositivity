module
public import SerrePositivity.KST.SConstruction.DGGluingCellRightAxisPerfectArrow
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.KST.SConstruction.DGPerfectComparisonHomGluing

/-!
概要：固定 cell source の同じ実右軸比較を指定商へ延長し実逆回転へ接続する。
方針：元二 Perf 関手と全比較を指定 dg 射で延長し、二実像を保つ実中央射を構成する。
規約：右制限の射影性の二証拠だけを明示入力に保持。
使われ方：同じ resolved 商包含を使う固定 S の実 LT 中央射。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (c : C) (hc : CategoryTheory.Limits.IsZero (ForgetEnrichment.of (Complex R) c))
  (h : DGGluingCellRightAxisProjectiveInput R C D M c hc)
local notation "B" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "P" => DGCategoryCellResolution.Source R (B)
variable (Q : Type z) [DGCategory R Q] [Small.{u} Q]

/-- 概要：同じ cell 右軸成分を指定 dg 射で元実 Perf 延長する。
方針：元の全 Hom graph 延長を合成する。
規約：指定射を保持。使われ方：実中央比較の商上の第一成分。 -/
def dgGluingCellRightAxisQuotientSource (q : DGFunctor R (P) Q) :
    DGFunctor R (P) (PerfectDGModule R Q) :=
  (dgGluingCellRightAxisPerfectSource R C D M c hc h).comp (perfectDGExtension R (P) Q q)

/-- 概要：同じ cell 恒等成分を指定 dg 射で元実 Perf 延長する。
方針：元の全 Hom graph 延長を合成する。
規約：指定射を保持。使われ方：実中央比較の商上の第二成分。 -/
def dgGluingCellRightAxisQuotientTarget (q : DGFunctor R (P) Q) :
    DGFunctor R (P) (PerfectDGModule R Q) :=
  (dgGluingCellRightAxisPerfectTarget R C D M c hc h).comp (perfectDGExtension R (P) Q q)

/-- 概要：同じ元右軸比較を指定商上の全 Perf dg 比較として保持する。
方針：元パラメータ付き全自然変換を同じ実延長で後合成する。
規約：全次数を保持。使われ方：同じ商上の実 Hom gluing 表示。 -/
def dgGluingCellRightAxisQuotientComparison (q : DGFunctor R (P) Q) :
    DGFunctorParamTrans R (P) (PerfectDGModule R Q) (𝟙_ (Complex R))
      (dgGluingCellRightAxisQuotientSource R C D M c hc h Q q)
      (dgGluingCellRightAxisQuotientTarget R C D M c hc h Q q) :=
  dgFunctorParamPost R (P) (PerfectDGModule R (P)) (PerfectDGModule R Q)
    (perfectDGExtension R (P) Q q) (dgGluingCellRightAxisPerfectComparison R C D M c hc h)

/-- 概要：同じ指定商上の実逆回転の共通小基底。
方針：元二実像と全 cone 像を保持する小模型を使う。
規約：全 Perf の Small 性を仮定しない。使われ方：実 LT 右面の新しい dg 基底。 -/
abbrev DGGluingCellRightAxisQuotientLiftBase (q : DGFunctor R (P) Q) :=
  DGPerfectComparisonInverseRotationBase R Q
    (dgGluingCellRightAxisQuotientSource R C D M c hc h Q q)
    (dgGluingCellRightAxisQuotientTarget R C D M c hc h Q q)

/-- 概要：同じ商上の実中央比較の終域である恒等 Hom gluing。
方針：同じ二実像・cone 像小基底の恒等二脚を使う。
規約：元対象を保持。使われ方：固定 S の中央射の実 dg 終域。 -/
abbrev DGGluingCellRightAxisQuotientLiftTarget (q : DGFunctor R (P) Q) :=
  let U := DGGluingCellRightAxisQuotientLiftBase R C D M c hc h Q q
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R U U
    (dgHomGluingBimodule R U U U (DGFunctor.id U) (DGFunctor.id U))

/-- 概要：同じ固定 cell source から指定商上の恒等 Hom gluing への実中央 dg 射。
方針：元右軸比較を指定商へ延長し、同じ実逆回転関手を適用する。
規約：元 cell source は不変。追加射影性以外の存在仮定を加えない。
使われ方：同じ resolved 商による固定 S 長方形の実中央辺。 -/
def dgGluingCellRightAxisQuotientLift (q : DGFunctor R (P) Q) :
    DGFunctor R (P) (DGGluingCellRightAxisQuotientLiftTarget R C D M c hc h Q q) :=
  dgPerfectComparisonInverseRotationFunctor R Q
    (dgGluingCellRightAxisQuotientSource R C D M c hc h Q q)
    (dgGluingCellRightAxisQuotientTarget R C D M c hc h Q q)
    (dgGluingCellRightAxisQuotientComparison R C D M c hc h Q q)
end SerrePositivity.KST.SConstruction

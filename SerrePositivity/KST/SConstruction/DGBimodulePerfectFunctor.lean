module
public import SerrePositivity.KST.SConstruction.DGPerfectModuleFunctorLift
public import SerrePositivity.KST.SConstruction.DGFunctorClosedComparison
public import SerrePositivity.DifferentialGraded.Bimodule.Category

/-!
概要：同じ実 bimodule と閉比較を、各右対象が射影的 perfect なら実 Perf dg 関手にする。
方針：抽象 bimodule の全 Hom を保った制限を先に検証し、具体的解像度へ適用する。
規約：元対象・元全 Hom・元閉射を保持。使われ方：cell graph 解像度の実比較。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  (C : Type w) [DGCategory R C]

/-- 概要：同じ右対象を保つ bimodule の実 Perf dg 関手。
方針：元左作用を射影的 perfect 対象へ制限する。
規約：元始域と全 Hom を保持。使われ方：実 graph 解像度の Perf 表示。 -/
def dgBimodulePerfectFunctor (M : BimoduleCategory R E C)
    (h : ∀ x, modulePerfectProjectiveOver R E Set.univ
      ((BimoduleCategory.underlying R E C M).rightAt x)) : DGFunctor R C (PerfectDGModule R E) :=
  dgPerfectModuleFunctorLift R E (BimoduleCategory.underlying R E C M) h

/-- 概要：同じ Perf 表示を含めると元 bimodule の左作用を厳密回収する。
方針：元制限関手の包含式を使う。規約：全 dg 関手の等号。
使われ方：元の実解像度との照合。 -/
lemma dgBimodulePerfectFunctor_inclusion (M : BimoduleCategory R E C)
    (h : ∀ x, modulePerfectProjectiveOver R E Set.univ
      ((BimoduleCategory.underlying R E C M).rightAt x)) :
    (dgBimodulePerfectFunctor R E C M h).comp (perfectDGModuleInclusion R E Set.univ) =
      BimoduleCategory.underlying R E C M :=
  dgPerfectModuleFunctorLift_inclusion R E (BimoduleCategory.underlying R E C M) h

variable (M N : BimoduleCategory R E C)
  (hM : ∀ x, modulePerfectProjectiveOver R E Set.univ
    ((BimoduleCategory.underlying R E C M).rightAt x))
  (hN : ∀ x, modulePerfectProjectiveOver R E Set.univ
    ((BimoduleCategory.underlying R E C N).rightAt x)) (a : M ⟶ N)

/-- 概要：同じ実 bimodule 射の成分を元の perfect 対象間へ制限する。
方針：元閉射族を同じ対象へ持ち上げる。規約：元射を保持。
使われ方：元 graph 比較の実成分。 -/
def dgBimodulePerfectMap (x : C) :
    ForgetEnrichment.of (Complex R) ((dgBimodulePerfectFunctor R E C M hM).obj x) ⟶
      ForgetEnrichment.of (Complex R) ((dgBimodulePerfectFunctor R E C N hN).obj x) :=
  dgPerfectModuleFunctorLiftComparisonMap R E
    (BimoduleCategory.underlying R E C M) (BimoduleCategory.underlying R E C N) hM hN a.val x

/-- 概要：元実 bimodule 射の全 Hom 自然性は同じ Perf 表示でも保持される。
方針：元の閉射族の全自然性を制限の抽象補題へ渡す。
規約：全次数を保持。使われ方：全 dg 比較への束ね。 -/
lemma dgBimodulePerfectMap_hom_naturality (x y : C) :
    (dgBimodulePerfectFunctor R E C M hM).map x y ≫
      eHomWhiskerLeft (Complex R)
        (ForgetEnrichment.of (Complex R) ((dgBimodulePerfectFunctor R E C M hM).obj x))
        (dgBimodulePerfectMap R E C M N hM hN a y) =
    (dgBimodulePerfectFunctor R E C N hN).map x y ≫
      eHomWhiskerRight (Complex R) (dgBimodulePerfectMap R E C M N hM hN a x)
        (ForgetEnrichment.of (Complex R) ((dgBimodulePerfectFunctor R E C N hN).obj y)) :=
  dgPerfectModuleFunctorLiftComparisonMap_hom_naturality R E
    (BimoduleCategory.underlying R E C M) (BimoduleCategory.underlying R E C N) hM hN a.val
    a.property x y

/-- 概要：同じ実 bimodule 射を単位パラメータの全 Perf dg 比較へ束ねる。
方針：元閉射族と同じ全 Hom 自然性を使う。
規約：元全比較を保持。使われ方：固定 cell source 上の実右軸比較。 -/
def dgBimodulePerfectComparison :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj (𝟙_ (Complex R)))
      (dgBimodulePerfectFunctor R E C M hM) (dgBimodulePerfectFunctor R E C N hN) :=
  dgFunctorClosedComparison R _ _ (dgBimodulePerfectMap R E C M N hM hN a)
    (dgBimodulePerfectMap_hom_naturality R E C M N hM hN a)
end SerrePositivity.KST.SConstruction

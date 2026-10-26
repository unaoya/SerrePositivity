module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisNativeSquare
public import SerrePositivity.KST.SConstruction.DGCellResolvedGraphExtendedNativeComparison

/-!
概要：同じ商値の native graph と保存済み右軸・恒等の実 Perf 延長を全比較する。
方針：同じ二 graph に実延長の包含比較を特殊化し、D の同じ射影性を用いる。
規約：中央 arrow 全比較・固定 ν の比較・長方形三認証は別工程。
使われ方：元右軸中央射の二成分を同じ実 Perf 模型で回収する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "P" => DGCategoryCellResolution.Source R (B)
local notation "Q" => DGQuotient.QuotientObject (P)
  (resolvedDGNullObjects R (B)
    (dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))))
local notation "ρ" => dgModuleResolvedInfinity R (RightModule R (P)) (P)
  (DGFunctor.id (RightModule R (P)))
local notation "E" => dgModuleExtensionInfinity R (P) (Q) (dgOdotMilnorResolvedInclusion R d)
local notation "I" => dgFullSubcategoryInclusion R (RightModule R (Q))
  (dgModuleSemifreeProperty R (Q))

/-- 概要：元右軸 graph の native 商値は同じ実 Perf 延長の包含像と全比較される。
方針：元の同じ graph・同じ商包含へ実延長比較を適用する。
規約：元の実対象と全 Hom を保持。使われ方：中央射の第一成分の模型照合。 -/
def dgOdotMilnorRightAxisPerfNativeSourceComparison : FunctorIso
    ((dgNerve.map (dgCellResolvedGraphModuleFunctor R (B)
      (dgOdotMilnorRightAxisEndofunctor R d)) ≫ (ρ)) ≫ (E) ≫ dgNerve.map (I))
    (dgNerve.map ((dgOdotMilnorRightAxisQuotientSource R d).comp
      (perfectDGModuleInclusion R (Q) Set.univ))) :=
  dgCellResolvedGraphPerfectExtendedNativeComparison.{u, u} R (B) (Q)
    (dgOdotMilnorRightAxisEndofunctor R d) (dgOdotMilnorResolvedInclusion R d)

/-- 概要：元恒等 graph の native 商値は同じ実 Perf 延長の包含像と全比較される。
方針：元の同じ graph・同じ商包含へ実延長比較を適用する。
規約：元の実対象と全 Hom を保持。使われ方：中央射の第二成分の模型照合。 -/
def dgOdotMilnorRightAxisPerfNativeTargetComparison : FunctorIso
    ((dgNerve.map (dgCellResolvedGraphModuleFunctor R (B) (DGFunctor.id (B))) ≫ (ρ)) ≫
      (E) ≫ dgNerve.map (I))
    (dgNerve.map ((dgOdotMilnorRightAxisQuotientTarget R d).comp
      (perfectDGModuleInclusion R (Q) Set.univ))) :=
  dgCellResolvedGraphPerfectExtendedNativeComparison.{u, u} R (B) (Q)
    (DGFunctor.id (B)) (dgOdotMilnorResolvedInclusion R d)

end SerrePositivity.KST.SConstruction

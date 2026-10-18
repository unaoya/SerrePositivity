module

public import SerrePositivity.KST.DerivedBlowup.OverlapComplexComparison
public import SerrePositivity.KST.DerivedBlowup.KoszulKFlat
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionComplexNaturality

/-!
概要：KST Def3.1 のチャート複体の導来スカラー拡大を Koszul 外積模型で計算する。
方針：証明済みの K-flat 性と既存の導来・項別スカラー拡大比較を使う。
規約：基底可換環上の underlying 複体の導来拡大。dg 代数の底変更比較は別工程。
使われ方：共通重なり環上でのチャート複体の導来比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u w w' w''

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {r : ℕ}

/-- 概要：チャート複体の導来スカラー拡大は像の関係式の外積複体で計算できる。
方針：K-flat 計算同型と項別底変更の外積比較を合成する。
規約：KST Def3.1、既存の導来圏を使う。
使われ方：導来重なり図式の underlying 複体の計算。 -/
def chartDerivedBaseChangeExteriorIso (a : Fin (r + 1) → R) (i : Fin (r + 1))
    (f : ChartRing R i →ₐ[R] B)
    [HasDerivedCategory.{w} (ModuleCat.{u} (ChartRing R i))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)] :
    (DifferentialGraded.ScalarExtension.complexDerivedExtension f.toRingHom).obj
        (DerivedCategory.Q.obj (derivedChartComplex a i)) ≅
      DerivedCategory.Q.obj
        (chartExteriorCochain (fun j => algebraMap R B (a j))
          (fun j => f (chartCoordinate R i j)) i) :=
  DifferentialGraded.ScalarExtension.complexDerivedExtensionKFlatIso f.toRingHom
    (derivedChartComplex a i) (derivedChartComplex_kFlat a i) ≪≫
      DerivedCategory.Q.mapIso (chartBaseChangeExteriorIso a i f)

/-- 概要：共通重なり環への導来スカラー拡大後の二つのチャート複体は同型。
方針：両側の K-flat 計算同型と実際の重なりでの複体同型を合成する。
規約：KST §3.1、比較は可換環上の導来圏。
使われ方：チャート図式の導来比較の underlying 複体部分。 -/
def overlapChartDerivedComplexIso (a : Fin (r + 1) → R) (i k : Fin (r + 1))
    [HasDerivedCategory.{w} (ModuleCat.{u} (ChartRing R k))]
    [HasDerivedCategory.{w'} (ModuleCat.{u} (ChartRing R i))]
    [HasDerivedCategory.{w''} (ModuleCat.{u} (OverlapRing R i k))] :
    (DifferentialGraded.ScalarExtension.complexDerivedExtension
      (overlapTransitionBase R i k).toRingHom).obj
        (DerivedCategory.Q.obj (derivedChartComplex a k)) ≅
      (DifferentialGraded.ScalarExtension.complexDerivedExtension
        (overlapInclusion R i k).toRingHom).obj
          (DerivedCategory.Q.obj (derivedChartComplex a i)) :=
  chartDerivedBaseChangeExteriorIso a k (overlapTransitionBase R i k) ≪≫
    DerivedCategory.Q.mapIso (overlapChartExteriorIso a i k) ≪≫
      (chartDerivedBaseChangeExteriorIso a i (overlapInclusion R i k)).symm

end SerrePositivity.KST.DerivedBlowup

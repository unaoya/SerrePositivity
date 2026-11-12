module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalHomValues
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalColumns

/-!
# 元の実 bar 比較の一点評価は複体の同型

## 概要
smallStrictBarTotalHom の一点評価を前向きの射とする複体同型を作る。

## 方針
元の shifted 因子の余積を始域と標的で比較する。逆は標的の余積の普遍性、
すなわち各次数の shift 同型・射列の余積・totalDesc の合成である。

## 規約
元の比較射を変更しない。擬同型や有界性を仮定しない。

## 使われ方
HA 1.2.4。既存の正規化 native 余錐を計算した実現へ移すための比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

/-- 元の graded bar の包含の各次数を、同じ MC bar の各次数の余積の脚として読む。 -/
def smallStrictBarSourceDegreeCofan (F : J ⥤ ModuleCategory A PUnit.{1}) (q : ℤ) :
    Cofan (fun s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) =>
      ((ForgetEnrichment.to (Complex A)
        (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s)).obj (op PUnit.unit)).X q) :=
  Cofan.mk (((dgCoherentBarModuleUnconditional A PUnit.{1}
    (smallStrictBarDiagram A F)).obj (op PUnit.unit)).X q) (fun s =>
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map
        (Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s)).f q)

/-- MC による微分の変更は各次数の台と余積包含を保つ。 -/
def smallStrictBarSourceDegreeCofan_isColimit (F : J ⥤ ModuleCategory A PUnit.{1}) (q : ℤ) :
    IsColimit (smallStrictBarSourceDegreeCofan A F q) := by
  let E := moduleEvaluation A PUnit.{1} PUnit.unit ⋙
    HomologicalComplex.eval (ModuleCat.{u} A) (.up ℤ) q
  exact isColimitCofanMkObjOfIsColimit E
    (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) _ (coproductIsCoproduct _)

/-- 各次数の shift と二段の余積による同型。 -/
def smallStrictBarTotalDegreeIso (F : J ⥤ ModuleCategory A PUnit.{1}) (q : ℤ) :
    ((dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)).obj (op PUnit.unit)).X q ≅
      ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)).X q :=
  (smallStrictBarSourceDegreeCofan_isColimit A F q).coconePointUniqueUpToIso
    (smallStrictBarDegreeCofan_isColimit A F q)

/-- 余積同型の前向きの射は、最初に指定した厳密な比較射の同じ成分である。 -/
theorem smallStrictBarTotalDegreeIso_hom (F : J ⥤ ModuleCategory A PUnit.{1}) (q : ℤ) :
    (smallStrictBarTotalDegreeIso A F q).hom =
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map (smallStrictBarTotalHom A F)).f q := by
  apply Cofan.IsColimit.hom_ext (smallStrictBarSourceDegreeCofan_isColimit A F q)
  intro s
  exact ((smallStrictBarSourceDegreeCofan_isColimit A F q).comp_coconePointUniqueUpToIso_hom
    (smallStrictBarDegreeCofan_isColimit A F q) (Discrete.mk s)).trans
      (smallStrictBarTotalHom_point_ι A F q s).symm

/-- 各次数の逆射は、totalDesc を用いて構成した標的の余積からの射である。 -/
theorem smallStrictBarTotalDegreeIso_inv (F : J ⥤ ModuleCategory A PUnit.{1}) (q : ℤ) :
    (smallStrictBarTotalDegreeIso A F q).inv =
      (smallStrictBarDegreeCofan_isColimit A F q).desc (smallStrictBarSourceDegreeCofan A F q) := rfl

/-- 一点評価した元の比較射を、そのまま前向きの射とする複体同型。 -/
def smallStrictBarTotalPointIso (F : J ⥤ ModuleCategory A PUnit.{1}) :
    (dgCoherentBarModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F)).obj (op PUnit.unit) ≅
      (smallStrictBarTotalTarget A F).obj (op PUnit.unit) := by
  let f := (moduleEvaluation A PUnit.{1} PUnit.unit).map (smallStrictBarTotalHom A F)
  letI : ∀ q : ℤ, IsIso (f.f q) := fun q => by
    change IsIso (((moduleEvaluation A PUnit.{1} PUnit.unit).map (smallStrictBarTotalHom A F)).f q)
    rw [← smallStrictBarTotalDegreeIso_hom A F q]
    infer_instance
  letI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

/-- この複体同型の前向きの射は元の一点評価そのもの。 -/
theorem smallStrictBarTotalPointIso_hom (F : J ⥤ ModuleCategory A PUnit.{1}) :
    (smallStrictBarTotalPointIso A F).hom =
      (moduleEvaluation A PUnit.{1} PUnit.unit).map (smallStrictBarTotalHom A F) := rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization

module

public import SerrePositivity.KST.Comparison.LoopFamily
public import SerrePositivity.KST.Spectra.PointedMappingParameters
public import SerrePositivity.KST.Spectra.PathSpace

/-!
# 基点に始まる区間の族の path space への写像

概要：任意のパラメータ付き区間写像を、始点が基点なら K-L9 の path space へ送る。
方針：区間を左因子へ交換し、点つき内部 Hom のパラメータ付き curry を使う。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13 の収縮から path space への比較。
使われ方：正則 bar の全空間の収縮の転置。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open scoped Simplicial

/--
概要：始点が基点である区間の族は、区間を左へ交換すると点つき写像族の条件を満たす。
方針：各単体で元の始点の等式を評価する。
規約：パラメータには基点を要求しない。
使われ方：点つき内部 Hom への curry の入力条件。
-/
theorem basedPathFamily_basepoint {X : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right)
    (h₀ : SSet.ι₀ ≫ f = SSet.const (PointedSimplicialSet.basepoint Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval.hom ▷ X ≫ (β_ (Δ[1] : SSet.{u}) X).hom ≫ f =
      toUnit ((𝟙_ SSet.{u}) ⊗ X) ≫ Y.hom := by
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro p
  have h := congrArg (fun t => t.app d p.2) (h₀.trans (const_basepoint X Y))
  exact h

/--
概要：基点に始まる区間の族から K-L9 の基点始点 path space への射。
方針：区間とパラメータを交換して、基点条件を持つ curry を使う。
規約：K-L9 の実際の pointedInterval と basedPathSpace を借りる。
使われ方：正則 bar から可縮な path space への比較。
-/
def basedPathFamilyMap {X : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right)
    (h₀ : SSet.ι₀ ≫ f = SSet.const (PointedSimplicialSet.basepoint Y)) :
    X ⟶ (Spectra.basedPathSpace Y).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y
    ((β_ (Δ[1] : SSet.{u}) X).hom ≫ f) (basedPathFamily_basepoint Y f h₀)

/--
概要：転置した path の族の基礎指数への包含は、元の区間の族の curry である。
方針：K-L9 のパラメータ付き curry の計算則を使う。
規約：両方のパラメータの順序を明示する。
使われ方：終点評価と標準ループ写像との比較。
-/
@[reassoc] theorem basedPathFamilyMap_ι {X : SSet.{u}} (Y : PointedSimplicialSet.{u})
    (f : X ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right)
    (h₀ : SSet.ι₀ ≫ f = SSet.const (PointedSimplicialSet.basepoint Y)) :
    basedPathFamilyMap Y f h₀ ≫ PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y =
      curry ((β_ (Δ[1] : SSet.{u}) X).hom ≫ f) :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι ..

end SerrePositivity.KST.Comparison

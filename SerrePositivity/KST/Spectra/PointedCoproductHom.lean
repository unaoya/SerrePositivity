module

public import SerrePositivity.KST.Spectra.CofiberMappingPullback
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.FunctionComplexProduct
public import SerrePositivity.KST.Spectra.GroupCochainHomotopyDiagram
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
概要：同じ源の点つき余積からの Hom を関数複体として表示する。
方針：反変 Hom が余積を積へ送ることと関数複体の積の普遍性を使う。
規約：点つき余積の添字集合は任意。
使われ方：Goerss–Jardine I §7、VIII §1。各セルの Hom の族への分解。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet Opposite

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：同じ点つき源の余積からの Hom の基礎単体集合は Hom の関数複体。
方針：余積の反対を積に移し、内部 Hom の極限保存を使う。
規約：係数の Kan 性は不要。
使われ方：Goerss–Jardine VIII §1。セルの Hom の積表示。 -/
def pointedCoproductHomUnderlyingIso (S : Type u) (P X : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom (∐ fun (_ : S) ↦ P) X).right ≅
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S (PointedObject.basedHom P X).right := by
  change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor X).obj (op (∐ fun (_ : S) ↦ P)) ≅
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.obj S ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor X).obj (op P))
  exact (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor X).mapIso (opCoproductIsoProduct (fun (_ : S) ↦ P)) ≪≫
    PreservesProduct.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor X) (fun (_ : S) ↦ op P) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.productIso S ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor X).obj (op P))

@[reassoc]
lemma pointedCoproductHomUnderlyingIso_eval (S : Type u) (P X : PointedSimplicialSet.{u})
    (s : S) :
    (pointedCoproductHomUnderlyingIso S P X).hom ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S (PointedObject.basedHom P X).right s =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (Limits.Sigma.ι (fun (_ : S) ↦ P) s) X := by
  have h : ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor X).mapIso
        (opCoproductIsoProduct (fun (_ : S) ↦ P)) ≪≫
      PreservesProduct.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor X) (fun (_ : S) ↦ op P) ≪≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.productIso S ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor X).obj (op P))).hom ≫
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor X).obj (op P)) s =
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor X).map (Limits.Sigma.ι (fun (_ : S) ↦ P) s).op := by
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.productIso_hom_eval, PreservesProduct.iso_hom,
      piComparison_comp_π]
    rw [← CategoryTheory.Functor.map_comp, opCoproductIsoProduct_hom_comp_π]
  exact h.trans (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.cofiberMappingFunctor_map X _)

/-- 概要：同じ源の点つき余積の Hom と Hom の関数複体の点つき同型。
方針：各座標への制限は点つきなので基点が座標ごとに一致する。
規約：関数複体の基点は Hom の基点の定数族。
使われ方：Goerss–Jardine I §7、VIII §1。fiber の正次数群の関数表示。 -/
def pointedCoproductHomIso (S : Type u) (P X : PointedSimplicialSet.{u}) :
    PointedObject.basedHom (∐ fun (_ : S) ↦ P) X ≅
      SimplicialFunctionComplex.pointedObj S (PointedObject.basedHom P X) :=
  Under.isoMk (pointedCoproductHomUnderlyingIso S P X) (by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.hom_ext
    intro s
    change (_ ≫ (pointedCoproductHomUnderlyingIso S P X).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S (PointedObject.basedHom P X).right s =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift (fun (_ : S) ↦ (PointedObject.basedHom P X).hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.eval S (PointedObject.basedHom P X).right s
    rw [Category.assoc, pointedCoproductHomUnderlyingIso_eval,
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.SimplicialFunctionComplex.lift_eval]
    exact Under.w (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (Limits.Sigma.ι (fun (_ : S) ↦ P) s) X))

end

end SerrePositivity.KST.Spectra

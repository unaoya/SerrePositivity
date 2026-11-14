module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchangeTarget
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.TensorExchangeBraid

/-!
概要：内部 Hom の二つのパラメータ交換は、列の構造に使う tensor strength と両立する。
方針：二度評価し、同じ因子交換と評価の自然性を比較する。
規約：閉対称モノイダル圏の恒等式。使われ方：二重 mapping 列の厳密なパラメータ交換。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.InternalHomExchange
end SerrePositivity.KST.Spectra.InternalHomExchange
namespace SerrePositivity.InfinityCategories.Project.PointedSpaces
open _root_.SerrePositivity.KST.Spectra.InternalHomExchange
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

/-- 二つのパラメータの交換と構造の strength の交換則。 -/
@[reassoc]
lemma mapping_strength (S A K E : C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S A ((ihom K).obj E) ≫
      (ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S K E) ≫ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K (S ⊗ E)).hom =
    S ◁ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K E).hom ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S K ((ihom A).obj E) ≫
      (ihom K).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S A E) := by
  apply uncurry_injective
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_ihom_map, _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom]
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc]
  have hev := congrArg (fun f => K ◁ f)
    ((ihom.ev A).naturality (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S K E))
  change K ◁ (A ◁ (ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S K E) ≫
      (ihom.ev A).app ((ihom K).obj (S ⊗ E))) =
    K ◁ ((ihom.ev A).app (S ⊗ (ihom K).obj E) ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S K E) at hev
  simp only [whiskerLeft_comp] at hev
  rw [← Category.assoc (K ◁ A ◁ (ihom A).map (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S K E)),
    hev, Category.assoc]
  rw [← whiskerLeft_comp_assoc K
    (A ◁ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S A ((ihom K).obj E)), _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.evaluation,
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.evaluation]
  simp only [whiskerLeft_comp, Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc K S ((ihom.ev A).app ((ihom K).obj E))]
  rw [← whiskerLeft_comp_assoc A (K ◁ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map S K ((ihom A).obj E)),
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.evaluation]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.map, uncurry_curry, whiskerLeft_comp, Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc A S ((ihom.ev K).app ((ihom A).obj E))]
  have hswap := congrArg (fun f => A ◁ f)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right K S (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K E).hom)
  simp only [whiskerLeft_comp] at hswap
  rw [← Category.assoc (A ◁ K ◁ S ◁ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K E).hom), hswap, Category.assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomTensorStrength.exchange_natural_right_assoc A S (K ◁ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K E).hom)]
  have he := congrArg (fun f => S ◁ f) (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.uncurry_uncurry_hom A K E)
  change S ◁ (A ◁ (K ◁ (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso A K E).hom ≫ (ihom.ev K).app ((ihom A).obj E)) ≫
    (ihom.ev A).app E) = _ at he
  simp only [whiskerLeft_comp, Category.assoc] at he
  rw [he]
  have hb := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.exchange_braid A K S ((ihom A).obj ((ihom K).obj E))
  have hc := congrArg (fun f => f ≫ S ◁ K ◁ (ihom.ev A).app ((ihom K).obj E) ≫
    S ◁ (ihom.ev K).app E) hb
  simpa only [Functor.id_obj, Functor.comp_obj, tensorLeft, curriedTensor,
    Functor.flip, Category.assoc] using hc

end SerrePositivity.InfinityCategories.Project.PointedSpaces

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.mapping_strength := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.mapping_strength

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.InternalHomExchange.mapping_strength_assoc := _root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.mapping_strength_assoc

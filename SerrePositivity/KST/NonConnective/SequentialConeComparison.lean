module

public import SerrePositivity.KST.NonConnective.SequentialResizedDiagramIso
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentOppositeEdge

/-!
概要：厳密な BF 錐全体の比較を、指定された coherent 錐全体の関手同型へ写す。
方針：追加始対象での比較も含む通常の自然変換を作り、同じ錐の形へ制限する。
規約：通常の極限性から ∞ 極限性への無条件の推論は行わない。
使われ方：置換列上で証明した ∞ 普遍性を、元の実余錐へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
namespace SerrePositivity.KST.NonConnective
variable {I : Type u} [SmallCategory I]
  {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {F G : I ⥤ C} (c : Cone F) (d : Cone G) (η : F ⟶ G) (m : c.pt ⟶ d.pt)
  (hm : ∀ i, m ≫ d.π.app i = c.π.app i ≫ η.app i)

/-- 元の頂点射と元の比較成分を全て保持した、追加始対象上の自然変換。 -/
def sequentialConeFunctorComparison : strictConeFunctor c ⟶ strictConeFunctor d where
  app x := match x with
    | .star => m
    | .of a => η.app (AsSmall.down.obj a)
  naturality x y f := by
    cases x with
    | star =>
      cases y with
      | star => exact (Category.id_comp _).trans (Category.comp_id _).symm
      | of a => exact (hm (AsSmall.down.obj a)).symm
    | of a =>
      cases y with
      | star => exact PEmpty.elim f
      | of b => exact η.naturality (AsSmall.down.map (WithInitial.down f))

/-- 同じ元の錐の全成分が可逆なら、coherent 錐全体の関手同型が得られる。 -/
def sequentialConeFunctorIso [∀ X Y : C, KanComplex (SimplicialCategory.sHom X Y)]
    (hη : ∀ i, IsInvertibleEdge (coherentNerveEdge (η.app i)))
    (hm' : IsInvertibleEdge (coherentNerveEdge m)) :
    FunctorIso (strictCoherentCone c).val (strictCoherentCone d).val := by
  let e : FunctorIso (resizedNerveMap (strictConeFunctor c) ≫ nerveToCoherent C)
      (resizedNerveMap (strictConeFunctor d) ≫ nerveToCoherent C) :=
    sequentialResizedFunctorIso (sequentialConeFunctorComparison c d η m hm) (by
    intro x
    cases x with
    | star => exact hm'
    | of a => exact hη (AsSmall.down.obj a))
  exact e.precomp
    (joinMap (𝟙 Δ[0]) ((nerveAsSmallIso I).hom ≫ nerveMap WithInitial.incl) ≫
      nerveInitialCone (WithInitial.starInitial (C := AsSmall.{v} I)))

end SerrePositivity.KST.NonConnective

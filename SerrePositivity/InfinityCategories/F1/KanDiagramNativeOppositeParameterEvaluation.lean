module

public import SerrePositivity.InfinityCategories.F1.KanDiagramNativeOppositeHomParameter
public import SerrePositivity.InfinityCategories.F1.LeftPointHomReverseComposition

/-!
概要：native な係数反転の対象ごとの値を、元の Kan 作用の反転パラメーターへ戻す。
方針：反転した内部 Hom の curry と、二重反転の自然性を厳密に照合する。
規約：元の strict Hom の全単体を保持し、その Kan 性は要求しない。
使われ方：weighted pointed prism の底と、実際の係数の同時評価との照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 元の作用を反転したパラメーターは、内部 Hom の標準反転で厳密に表せる。 -/
lemma leftPointHomReverseParameter_uncurry_eq {X Y H : SSet.{u}}
    (g : H ⟶ (ihom X).obj Y) :
    leftPointHomReverseParameter (uncurry g) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (g ≫ (SSet.opFunctorCompOpFunctorIso.app ((ihom X).obj Y)).inv ≫
          SSet.opFunctor.map (oppositeInternalHomIso X Y).hom) ≫
        (uliftOppositeIso ((ihom X.op).obj Y.op)).hom := by
  have hc : curry ((oppositeTensorIso X H).inv ≫ SSet.opFunctor.map (uncurry g)) =
      SSet.opFunctor.map g ≫ (oppositeInternalHomIso X Y).hom := by
    apply uncurry_injective
    rw [uncurry_curry, oppositeInternalHom_map_uncurry]
    rfl
  have hn := SSet.opFunctorCompOpFunctorIso.inv.naturality g
  change g ≫ (SSet.opFunctorCompOpFunctorIso.app ((ihom X).obj Y)).inv =
    (SSet.opFunctorCompOpFunctorIso.app H).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map g) at hn
  have hb : (SSet.opFunctorCompOpFunctorIso.app H).inv ≫
      SSet.opFunctor.map (SSet.opFunctor.map g ≫ (oppositeInternalHomIso X Y).hom) =
      g ≫ (SSet.opFunctorCompOpFunctorIso.app ((ihom X).obj Y)).inv ≫
        SSet.opFunctor.map (oppositeInternalHomIso X Y).hom := by
    rw [SSet.opFunctor.map_comp, ← Category.assoc, ← hn, Category.assoc]
  rw [leftPointHomReverseParameter, hc, hb]

/-- native な係数反転の各値は、元の変換の評価を反転した同じパラメーター。 -/
lemma kanDiagramNativeOppositeHomParameter_pointwise
    {I : Type u} [SmallCategory I] (F G : KanDiagramObject I) (i : I) :
    (SSet.uliftFunctor.{u + 1, u}).map (kanDiagramNativeOppositeHomParameter F G) ≫
      (SSet.uliftFunctor.{u + 1, u}).map (SSet.opFunctor.map
        (strictDiagramMappingComponent ((F.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget)
          ((G.val ⋙ kanObjectOpFunctor) ⋙ kanObjectForget) i)) ≫
      (uliftOppositeIso ((ihom (F.val.obj i).obj.op).obj (G.val.obj i).obj.op)).hom =
    leftPointHomReverseParameter (uncurry
      (strictDiagramMappingComponent (F.val ⋙ kanObjectForget) (G.val ⋙ kanObjectForget) i)) := by
  rw [← Category.assoc, ← Functor.map_comp,
    kanDiagramNativeOppositeHomParameter_component]
  exact (leftPointHomReverseParameter_uncurry_eq
    (strictDiagramMappingComponent (F.val ⋙ kanObjectForget)
      (G.val ⋙ kanObjectForget) i)).symm

end SerrePositivity.InfinityCategories

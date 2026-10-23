module

public import SerrePositivity.InfinityCategories.F1.Coherent.LeftFlagIso
public import SerrePositivity.InfinityCategories.F1.Coherent.LeftResolutionComparison

/-!
概要：左 Hom の具体的な旗の表示における標準比較射の同定。
方針：反対 nerve の往復と端点の等号による移送を消し、右 Hom の旗の計算へ還元する。
規約：比較射そのものの等号を示し、同値の存在だけには置き換えない。
使われ方：Kerodon Proposition 4.6.7.16、Corollary 5.6.0.6、左 fiber の比較の高次の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：反転前の右 Hom 比較を反対圏へ戻すと標準の coherent Hom 比較になる。
方針：二つの端点の移送は元の単体を保ち、nerve の同型の往復が消えることを使う。
規約：Kan 性を要求しない。
使われ方：Kerodon §4.6.7、左 Hom 比較の具体的な解像への表示。 -/
lemma coherentOppositeRightHomComparison_pinchedIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (x y : C) :
    HomotopyLimits.coherentOppositeRightHomComparison x y ≫
      (coherentOppositePinchedIso x y).hom =
    coherentHomComparison (Opposite.op y) (Opposite.op x) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  apply PinchedHom.Simplex.ext
  change ((eqToHom (congrArg₂ (fun a b ↦ pinchedHom a b)
    (HomotopyLimits.coherentNerveOppositeMap_vertex y)
    (HomotopyLimits.coherentNerveOppositeMap_vertex x))).app _
      ((pinchedHomMap (HomotopyLimits.coherentNerveOppositeMap C) _ _).app _
        ((HomotopyLimits.coherentOppositeHomEndpointIso x y).hom.app _
          ((pinchedHomMap (HomotopyLimits.coherentNerveOppositeInverse C) _ _).app _
            ((coherentHomComparison (Opposite.op y) (Opposite.op x)).app _ s))))).val = _
  rw [pinchedHom_eqToHom_app_val
    (HomotopyLimits.coherentNerveOppositeMap_vertex y)
    (HomotopyLimits.coherentNerveOppositeMap_vertex x)]
  change (HomotopyLimits.coherentNerveOppositeMap C).app (Opposite.op ⦋n + 1⦌)
    (((HomotopyLimits.coherentOppositeHomEndpointIso x y).hom.app _
      ((pinchedHomMap (HomotopyLimits.coherentNerveOppositeInverse C) _ _).app _
        ((coherentHomComparison (Opposite.op y) (Opposite.op x)).app _ s))).val) = _
  dsimp only [HomotopyLimits.coherentOppositeHomEndpointIso, eqToIso.hom]
  rw [pinchedHom_eqToHom_app_val
    (HomotopyLimits.coherentNerveOppositeInverse_vertex y)
    (HomotopyLimits.coherentNerveOppositeInverse_vertex x)]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (HomotopyLimits.coherentNerveOppositeIso C).inv_hom_id _)
    ((coherentHomComparison (Opposite.op y) (Opposite.op x)).app _ s).val

/-- 概要：左 Hom の比較射は旗の表示で右解像の標準比較の反転になる。
方針：反対 nerve の往復を消し、右 Hom 比較の旗の計算を反転する。
規約：持ち上げる宇宙と反転の交換は標準同型を使う。
使われ方：Kerodon Proposition 4.6.7.16、Corollary 5.6.0.6、左 fiber の比較射の同定。 -/
lemma coherentLeftHomComparison_flagIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (x y : C) :
    HomotopyLimits.coherentLeftHomComparison x y ≫
      (coherentLeftPinchedFlagIso x y).hom =
    (SSet.uliftFunctor.{v, u}).map
      (SSet.opFunctor.map (coherentResolutionComparison (SimplicialCategory.sHom x y))) := by
  have h : HomotopyLimits.coherentOppositeRightHomComparison x y ≫
      (coherentOppositePinchedIso x y).hom ≫
      (coherentPinchedFlagIso (Opposite.op y) (Opposite.op x)).hom =
      (SSet.uliftFunctor.{v, u}).map
        (coherentResolutionComparison (SimplicialCategory.sHom x y)) := by
    rw [← Category.assoc, coherentOppositeRightHomComparison_pinchedIso]
    exact coherentHomComparison_flagIso (Opposite.op y) (Opposite.op x)
  change (HomotopyLimits.uliftOppositeIso (SimplicialCategory.sHom x y)).hom ≫
    SSet.opFunctor.map (HomotopyLimits.coherentOppositeRightHomComparison x y ≫
      (coherentOppositePinchedIso x y).hom ≫
      (coherentPinchedFlagIso (Opposite.op y) (Opposite.op x)).hom) ≫
    (HomotopyLimits.uliftOppositeIso
      (coherentResolutionRightAdjoint.obj (SimplicialCategory.sHom x y))).inv = _
  rw [h]
  rfl

/-- 概要：左 coslice fiber の比較も旗の座標では標準比較の反転になる。
方針：fiber と左 Hom の標準同型の往復を消す。
規約：fiber の比較射は既存の coherentCosliceFiberComparison をそのまま使う。
使われ方：Kerodon Corollary 5.6.0.6、普遍 left fibration の fiber 比較の同定。 -/
lemma coherentCosliceFiberComparison_flagIso
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (x y : C) :
    HomotopyLimits.coherentCosliceFiberComparison x y ≫
      (pinchedLeftCosliceFiberIso (coherentNerveVertex x) (coherentNerveVertex y)).inv ≫
      (coherentLeftPinchedFlagIso x y).hom =
    (SSet.uliftFunctor.{v, u}).map
      (SSet.opFunctor.map (coherentResolutionComparison (SimplicialCategory.sHom x y))) := by
  rw [HomotopyLimits.coherentCosliceFiberComparison, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact coherentLeftHomComparison_flagIso x y

end SerrePositivity.InfinityCategories

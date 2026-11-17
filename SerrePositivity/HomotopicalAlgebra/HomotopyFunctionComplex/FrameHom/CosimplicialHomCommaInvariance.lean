module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallCosimplicialHomElements
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallNerveInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.OppositeElementsInvariance
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage

/-!
# 元の Hom の不変性から小さい comma の不変性へ

概要：元の cosimplicial Hom で反転される右対象の射は、小さい comma でも反転。
方針：同じ反対要素圏の nerve の不変性・宇宙比較・元の自然な表示同値を合成。
規約：元の右対象の射を保持し、単体集合モデルや Hom の Kan 性は要求しない。
使われ方：元の分解の全右脚の小さい Cat 値図式の各遷移の不変性。
-/

@[expose] public section
universe u v w
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements
open _root_.SerrePositivity.HomotopyFunctionComplex _root_.SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C)

/-- 元の右対象の射の Hom での不変性を、同じ小さい comma の射へ移す。 -/
lemma smallCommaMap_localized_isIso {V W : C} (f : V ⟶ W)
    (hf : IsIso (AnodyneHomotopy.anodyneQ.map ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f))) :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap
      (CostructuredArrow.map (S := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallDiagram.{u, v, w} A) (AsSmall.up.map f)))) := by
  let Q := AnodyneHomotopy.anodyneQ.{max w u v}
  have hs : IsIso (Q.map (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallElementsMap.{u, v, w} A f))) :=
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SmallNerve.map_localized_isIso.{v, 0, max w u v}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map f).mapElements.op
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.map_localized_isIso _ hf)
  have hV : IsIso (Q.map (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma.{u, v, w} A V))) :=
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage.imageIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallEquivalence.{u, v, w} A V) Q
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom
  have hW : IsIso (Q.map (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma.{u, v, w} A W))) :=
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveEquivalenceImage.imageIso (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallEquivalence.{u, v, w} A W) Q
      (Localization.inverts _ SSet.anodyneExtensions)).isIso_hom
  have h : nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallElementsMap.{u, v, w} A f) ≫ nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma A W) =
      nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma A V) ≫ nerveMap
        (CostructuredArrow.map (S := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallDiagram A) (AsSmall.up.map f)) := by
    change nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallElementsMap A f ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma A W) =
      nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma A V ⋙ CostructuredArrow.map (AsSmall.up.map f))
    rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma_naturality]
  have hq := congrArg Q.map h
  rw [Q.map_comp, Q.map_comp] at hq
  have hc : IsIso (Q.map (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallToComma.{u, v, w} A V)) ≫ Q.map
      (nerveMap (CostructuredArrow.map (S := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements.smallDiagram A) (AsSmall.up.map f)))) :=
    hq ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hc

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CosimplicialHomElements

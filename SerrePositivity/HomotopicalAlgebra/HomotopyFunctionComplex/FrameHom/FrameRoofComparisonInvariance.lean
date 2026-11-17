module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLeftRoofPrecompose
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameIndexAugmentation
/-! 概要：元の frame 比較を全要素圏の実 roof とその反転性へ移す。
方針：元の四列比較と同じ終端 augmentation の全自然性を使う。
規約：元の全 frame・augmentation・比較射とパラメータを保持する。
使われ方：標準自由 Hom span から元の全 pinched 族の弱同値性を検出する。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.SerrePositivity.EInfinity.Hammock
open _root_.SerrePositivity.HomotopyFunctionComplex _root_.SerrePositivity.SimplicialModel
variable {C : Type u} [Category.{v} C] {X Y : C}
  (A' A : SimplexCategory ⥤ C) (α : A' ⟶ A)

/-- 概要：元の Hom 比較の反転性は同じ全要素圏写像の反転性を与える。
方針：元の両 augmentation を消去する。
規約：同じ Hom の全係数射を保持。使われ方：共通 frame の全族比較。 -/
lemma frameSpanSourceIndexMap_localized_isIso
    (hα : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.uliftFunctor.{max u v, v}.map
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y)))) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap (Y := Y) A' A α))) := by
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_localized_isIso.{v, max u v}
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A').obj Y)
  have := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_localized_isIso.{v, max u v}
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)
  have h := congrArg AnodyneHomotopy.anodyneQ.map
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation_naturality.{v, max u v}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap α).app Y))
  simp only [Functor.map_comp] at h
  change AnodyneHomotopy.anodyneQ.map
    (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap (Y := Y) A' A α)) ≫
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation.{v, max u v}
      ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A').obj Y)) = _ at h
  have hc : IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap (Y := Y) A' A α)) ≫
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.SimplexTerminalNerve.liftedAugmentation.{v, max u v}
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A').obj Y))) := by
    rw [h]
    infer_instance
  exact (isIso_comp_right_iff _ _).mp hc

variable (W : MorphismProperty C) [W.IsMultiplicative]
  (p' : A' ⟶ (Functor.const SimplexCategory).obj X) (hp' : ∀ n, W (p'.app n))
  (p : A ⟶ (Functor.const SimplexCategory).obj X) (hp : ∀ n, W (p.app n))
  (hA' : ∀ {i j} (a : i ⟶ j), W (A'.map a))
  (hA : ∀ {i j} (a : i ⟶ j), W (A.map a))
  (hα : α ≫ p = p')

include hα in
/-- 概要：同じ始域の元の frame 比較は全 roof の可換式を与える。
方針：元の四列比較で始域射を恒等に取り、厳密な単位則を使う。
規約：元の全要素圏と同じ比較射を保持。使われ方：標準自由 Hom span の接続。 -/
lemma frameLeftRoofColimitMap_comparison :
    AnodyneHomotopy.anodyneQ.map
      (nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameSpanSourceIndexMap (Y := Y) A' A α)) ≫
      AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap W A' p' hp' hA') =
    AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap (Y := Y) W A p hp hA) := by
  have he : α ≫ p = p' ≫ (Functor.const SimplexCategory).map (𝟙 X) := by
    apply NatTrans.ext
    funext n
    change α.app n ≫ p.app n = p'.app n ≫ 𝟙 X
    exact (NatTrans.congr_app hα n).trans (Category.comp_id _).symm
  have h := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.frameLeftRoofColimitMap_precompose (Y := Y) W A' A p' hp' p hp hA' hA α
    (𝟙 X) he
  rw [Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.arrowMap_identity, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.precomposePointMap_unit] at h
  have hid := AnodyneHomotopy.anodyneQ.map_id (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y)
  rw [hid, Category.comp_id] at h
  exact h

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom

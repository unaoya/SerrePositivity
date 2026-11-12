module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionFront
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceIntervalComparison

/-!
概要：右 prism による区間比較を coherent 単体の切断制限として計算する。
方針：標準単体への自然性と join の標準同型で一般の単体へ戻す。
規約：パラメーターは任意の単体集合。
使われ方：合成 prism の射影の全パラメーター付き同定。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：右 prism に沿う任意の join 図式の評価は切断写像による制限。
方針：パラメーター単体の Yoneda 射に自然性を適用し、標準単体の場合へ帰着する。
規約：固定終点や quasicategory 性は要求しない。
使われ方：coherent Hom の区間比較の全単体での計算。 -/
lemma rightMappingSpacePrism_evaluate {A X : SSet.{u}} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A Δ[0] ⟶ X)
    {n : ℕ} (a : A _⦋n⦌) (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    F.app (Opposite.op ⦋n⦌) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A).app (Opposite.op ⦋n⦌) (t, a)) =
      X.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut (stdSimplex.objEquiv t).toOrderHom)).op
        (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 Δ[0]) ≫ F)) := by
  let f := SSet.yonedaEquiv.symm a
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[0]) ≫ F
  let b := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism Δ[n]).app (Opposite.op ⦋n⦌)
    (t, SSet.yonedaEquiv (𝟙 Δ[n]))
  have hn := congrArg (fun h ↦ h (t, SSet.yonedaEquiv (𝟙 Δ[n])))
    (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism_naturality f) (Opposite.op ⦋n⦌))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A).app (Opposite.op ⦋n⦌)
      (t, f.app (Opposite.op ⦋n⦌) (SSet.yonedaEquiv (𝟙 Δ[n]))) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[0])).app (Opposite.op ⦋n⦌) b at hn
  rw [SSet.yonedaEquiv_symm_app_id] at hn
  rw [hn, ← SSet.yonedaEquiv_symm_app_objEquiv_symm, Equiv.symm_apply_apply]
  change g.app (Opposite.op ⦋n⦌) b = ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ g).app
    (Opposite.op ⦋n⦌) _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.rightMappingSpacePrism_stdSimplex_cut n t]
  change g.app (Opposite.op ⦋n⦌) b =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ g).app
      (Opposite.op ⦋n⦌) b
  rw [Iso.hom_inv_id_assoc]

/-- 概要：右 Hom の族を展開した join 図式の標準単体表示は元の pinched 単体。
方針：curry・uncurry の逆写像則を各単体で評価する。
規約：パラメーター単体も固定端点も任意。
使われ方：右 Hom の区間比較の元の coherent 単体への還元。 -/
lemma pinchedHomUncurry_simplex {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) {n : ℕ} (a : A _⦋n⦌) :
    SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 Δ[0]) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry f) =
        (f.app (Opposite.op ⦋n⦌) a).val := by
  have h := congrArg (fun g : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ↦
    (g.app (Opposite.op ⦋n⦌) a).val) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomCurry_uncurry f)
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomCurry at h
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).inv.app (Opposite.op ⦋n⦌) _).val = _ at h
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomSliceFiberIso_inv_app] at h
  exact h

/-- 概要：右 Hom の区間比較の評価は元の pinched 単体の切断制限。
方針：任意の join 図式の prism の公式へ curry・uncurry の座標を代入する。
規約：全次数のパラメーター単体を同時に扱う。
使われ方：coherent な合成 prism の射影の同定。 -/
lemma pinchedHomToIntervalMappingSpace_evaluate {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) {n : ℕ} (a : A _⦋n⦌)
    (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y)).app
      (Opposite.op ⦋n⦌) (t, a) =
    X.map (SimplexCategory.mkHom (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPrismCut (stdSimplex.objEquiv t).toOrderHom)).op
      (f.app (Opposite.op ⦋n⦌) a).val := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_uncurry]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomUncurry f).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.rightMappingSpacePrism A).app (Opposite.op ⦋n⦌) (t, a)) = _
  rw [rightMappingSpacePrism_evaluate, pinchedHomUncurry_simplex]

/-- 概要：合成 prism の射影は第一の射の既存の区間比較と一致する。
方針：各単体を前面に制限し、切断の coherent 単体の二つの表示を一致させる。
規約：第二の Hom パラメーターを含む全パラメーターの等式。
使われ方：右 slice の合成 prism を普遍輸送と比較するための底の式。 -/
lemma coherentCompositionPrism_projection {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y Z : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionPrism X Y Z ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Z)) =
    (Δ[1] ◁ fst _ _) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, σ, τ⟩
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[n] Δ[0] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫
    SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex σ.down τ.down
      (stdSimplex.objEquiv t).toOrderHom)) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.joinStdSimplexIso_rightPoint_inl,
    SSet.yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex_front]
  exact (pinchedHomToIntervalMappingSpace_evaluate (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparison X Y) σ t).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

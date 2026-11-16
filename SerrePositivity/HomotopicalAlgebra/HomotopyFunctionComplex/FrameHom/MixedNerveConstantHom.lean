module
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveNatTransFunctor
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.NerveNatTransCylinder
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses
/-!
概要：元の定値自然変換の全円柱を同じ成分辺の定値族へ同定する。
方針：全次数の通常円柱を計算し、元の成分辺の定値写像と照合する。
規約：元の自然変換・元の辺・全パラメータを保持する。
使われ方：元の自由単位の全図式制限を標準単位の定値族へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
/-- 概要：元の定値自然変換円柱は同じ成分辺を全パラメータで一定にした写像。
方針：通常の uncurry の全対象・全射を計算する。
規約：任意の添字圏を保持。使われ方：定値単位二胞体の回収。 -/
lemma homotopy_const_h {I C : Type (u + 1)} [Category.{u} I] [Category.{u} C]
    {x y : C} (f : x ⟶ y) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy ((Functor.const I).map f)).h =
      snd (nerve I) (Δ[1] : SSet.{u + 1}) ≫ SSet.yonedaEquiv.symm (nerve.edgeMk f).edge := by
  have he : Functor.uncurry.obj
      (ComposableArrows.mk₁ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.liftedNatTrans ((Functor.const I).map f))) ⋙
        ULiftHom.down.{u, u + 1, u + 1} =
      CategoryTheory.Prod.fst (Fin 2) (ULiftHom.{u + 1} I) ⋙ ComposableArrows.mk₁ f := by
    refine CategoryTheory.Functor.ext (fun p => ?_) ?_
    · rcases p with ⟨k, i⟩
      fin_cases k <;> rfl
    · rintro ⟨k,i⟩ ⟨l,j⟩ a
      have hkl := leOfHom a.1
      fin_cases k <;> fin_cases l <;>
        simp_all only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, Functor.comp_obj,
          Functor.uncurry_obj_obj, ComposableArrows.mk₁_obj, ComposableArrows.Mk₁.obj,
          Fin.mk_one, Functor.comp_map, Functor.uncurry_obj_map, ComposableArrows.mk₁_map,
          ComposableArrows.Mk₁.map, Prod.fst_obj, eqToHom_refl,
          Prod.fst_map, Category.comp_id, Category.id_comp, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.lifted, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.liftedNatTrans,
          ULiftHom.up, ULiftHom.down, Functor.const_obj_map, NatTrans.id_app,
          Functor.whiskerLeft_app, Functor.whiskerRight_app]
      all_goals first | omega | rfl | exact Category.comp_id f
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro z
  change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.liftedNatTrans ((Functor.const I).map f))).h.app n
      ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.up I).app n z.1, z.2) ⋙ ULiftHom.down = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.nerveNatTransHomotopy_app, Functor.assoc, he]
  rfl

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve

universe v
namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom
open _root_.CategoryTheory _root_.SSet _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.SerrePositivity.InfinityCategories
open scoped _root_.Simplicial

/-- 概要：同じ成分辺に全パラメータで一定な円柱は、その射の定値二胞体を表す。
方針：定値関手への写像で元の辺を送り、全円柱の一次単体を比較する。
規約：端点表示は全 Arrow 等式で保持。使われ方：定値単位の端点輸送。 -/
lemma constantFamilyHom_arrow_of_h_eq {K X : SSet.{v}} {U V : K ⟶ X}
    {x y : X.obj (Opposite.op (SimplexCategory.mk 0))}
    (H : SSet.Homotopy U V) (e : Truncated.Edge (X := (truncation 2).obj X) x y)
    (h : H.h = snd K (Δ[1] : SSet.{v}) ≫ SSet.yonedaEquiv.symm e.edge) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk e)) := by
  let e' : Truncated.Edge (X := (truncation 2).obj ((ihom K).obj X))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const x : K ⟶ X)) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const y : K ⟶ X)) :=
    { edge := (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X))).edge
      src_eq := (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X))).src_eq.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex K x)
      tgt_eq := (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X))).tgt_eq.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex K y) }
  have hc : Truncated.HomotopyCategory.homMk e' =
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap K (Truncated.HomotopyCategory.homMk e) := by
    symm
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap, hoFunctor_map, Functor.toCatHom_toFunctor,
      mapHomotopyCategory, Truncated.mapHomotopyCategory_homMk] using
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homMk_transport (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex K x) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap_vertex K y)
        (e.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X))) e' rfl)
  have hh : H.h = uncurry (SSet.yonedaEquiv.symm e'.edge) := by
    change H.h = uncurry (SSet.yonedaEquiv.symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap K X).app (Opposite.op ⦋1⦌) e.edge))
    rw [h, ← SSet.yonedaEquiv_symm_comp, uncurry_natural_left]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorMap, uncurry_curry]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro z
    rfl
  have he : (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H).edge = e'.edge := by
    change SSet.yonedaEquiv (curry H.h) = _
    rw [hh, curry_uncurry]
    exact SSet.yonedaEquiv.apply_symm_apply _
  exact (Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ he).trans
    (congrArg Arrow.mk hc)

/-- 概要：元の定値自然変換の任意の後合成は、同じ成分射の像の定値二胞体。
方針：元の全円柱式を後合成し、同じ辺の定値族の Arrow 比較へ渡す。
規約：任意の実後合成を保持。使われ方：実 D(R) の定値単位・augmentation。 -/
lemma mixedNerve_const_postcomp_arrow {I C : Type (u + 1)}
    [Category.{u} I] [Category.{u} C] {x y : C} (f : x ⟶ y)
    {D : SSet.{u + 1}} (q : nerve C ⟶ D) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy ((Functor.const I).map f)) q))) =
    Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap (nerve I)
      (Truncated.HomotopyCategory.homMk ((nerve.edgeMk f).map q).toTruncated)) := by
  apply _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.constantFamilyHom_arrow_of_h_eq
  change (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy ((Functor.const I).map f)).h ≫ q = _
  rw [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy_const_h, Category.assoc, SSet.yonedaEquiv_symm_comp]
  rfl

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom

module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.FixedCoconeReindexHom
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ChosenSymmetricSuspension

/-! # 固定 span の再添字付けと suspension の交換

概要：転置で span が変わらない suspension では、再添字付けの標準頂点自己同型は swapIso である。
方針：再添字付けた余錐と転置余錐の値を形状の交換則で同定し、標準比較の一致を使う。
規約：端点の表示変更を含め Arrow の等号で比較する。使われ方：余錐空間の交換作用と負号の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：等号による終点の輸送を後に付けても Arrow としての射は同じ。
方針：等号の帰納法で恒等射との合成に戻す。
規約：任意の圏の射。使われ方：頂点表示を元へ戻す標準自己同型の比較。 -/
lemma stableArrow_comp_eqToHom {C : Type*} [Category* C] {x y z : C}
    (f : x ⟶ y) (h : y = z) : Arrow.mk (f ≫ eqToHom h) = Arrow.mk f := by
  subst z
  simp only [eqToHom_refl, Category.comp_id]

/-- 概要：比較先の余極限余錐の等号は標準頂点比較の Arrow の等号を与える。
方針：余錐の等号を消す。
規約：余極限性の証明の選択には依存しない。使われ方：交換後の余錐の二つの表示の照合。 -/
lemma stableColimitVertexIso_congr_target_arrow {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c d e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d)
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone e) (h : d = e) :
    (Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso c d hc hd).hom : Arrow (hoFunctor.obj X)) =
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso c e hc he).hom := by
  subst e
  rfl

/-- 概要：転置前後で span が等しければ span 自体が二枝交換で不変。
方針：転置した span の計算則と指定の等号を合成する。
規約：値域の quasicategory 性は不要。使われ方：同じ図式上での余錐空間の交換。 -/
lemma SuspensionSquare.spanSwap_fixed {X : SSet.{u}} {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.transpose.square = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square) :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pushoutSpan_transpose s.square).symm.trans h

/-- 概要：固定 span 内で再添字付けた suspension の余錐は転置した余錐の同じ表示。
方針：余錐の値を比較し、span 交換と正方形転置の形状の公式を使う。
規約：余錐の部分型の等号。使われ方：二種類の標準頂点比較の照合。 -/
lemma SuspensionSquare.pushoutCocone_reindexFixed_spanSwap {X : SSet.{u}} {x : X _⦋0⦌}
    (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x) (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.transpose.square = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square).reindexFixed _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (s.spanSwap_fixed h) =
      s.transposedCoconeOfSameSpan h := by
  apply Subtype.ext
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (𝟙 (Δ[0] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ s.square) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ ((β_ (Δ[1] : SSet.{u}) Δ[1]).hom ≫ s.square)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanCoconeSquareIso_swap, Category.assoc]

/-- 概要：固定 span の再添字付けによる頂点自己同型は suspension の swapIso に一致する。
方針：終点表示の輸送を除き、交換後の余錐を転置余錐へ同定する。
規約：転置前後の span の等号を仮定する。使われ方：余錐空間の自己作用を既存の交換へ結ぶ。 -/
lemma SuspensionSquare.fixedReindexVertexIso_eq_swapIso_arrow
    {X : SSet.{u}} [Quasicategory X] {x : X _⦋0⦌} (s : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SuspensionSquare x)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.transpose.square = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan s.square) :
    (Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeReindexVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square) s.isPushout _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap
      (s.spanSwap_fixed h) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_comp_self).hom : Arrow (hoFunctor.obj X)) =
      Arrow.mk s.swapIso.hom := by
  change Arrow.mk ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitVertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square).reindexFixed _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (s.spanSwap_fixed h)) s.isPushout
      (s.isPushout.reindexFixed _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (s.spanSwap_fixed h) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_comp_self)).hom ≫
        eqToHom (congrArg (fun x => (SSet.HomotopyCategory.mk x : hoFunctor.obj X))
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square).vertex_reindexFixed _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (s.spanSwap_fixed h)))) = _
  rw [stableArrow_comp_eqToHom]
  exact (stableColimitVertexIso_congr_target_arrow (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone s.square).reindexFixed _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (s.spanSwap_fixed h))
    (s.transposedCoconeOfSameSpan h) s.isPushout
    (s.isPushout.reindexFixed _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap (s.spanSwap_fixed h) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_comp_self)
    (s.transposedCoconeOfSameSpan_isColimit h) (s.pushoutCocone_reindexFixed_spanSwap h)).trans
      (s.swapIso_eq_colimitVertexIso_arrow_of_sameSpan h).symm

/-- 概要：各頂点の対称模型では余錐空間の再添字付けの頂点作用が swapIso である。
方針：対称模型の転置前後の span の等号を一般の同定へ与える。
規約：追加の span の等号は不要。使われ方：対称模型の交換をループ模型へ移す。 -/
lemma chosenSymmetricSuspensionSquare_reindex_swap_arrow
    {X : SSet.{u}} [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] (x : X _⦋0⦌) :
    (Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.fixedCoconeReindexVertexIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSymmetricSuspensionSquare x).square)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSymmetricSuspensionSquare x).isPushout _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSymmetricSuspensionSquare x).spanSwap_fixed
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSymmetricSuspensionSquare_sameSpan x)) _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanSwap_comp_self).hom :
        Arrow (hoFunctor.obj X)) = Arrow.mk (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSymmetricSuspensionSquare x).swapIso.hom :=
  (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSymmetricSuspensionSquare x).fixedReindexVertexIso_eq_swapIso_arrow
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenSymmetricSuspensionSquare_sameSpan x)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories

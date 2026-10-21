module

public import SerrePositivity.InfinityCategories.F2.FunctorIsoDownAlgebra

/-!
概要：二射の指定比較の水平合成は、元の端点表示を保って宇宙下降と可換する。
方針：中間の端点補正を分配し、下降の合成・前後合成の式を適用する。
規約：元の指定二同型を保持。使われ方：native 二射の合成比較を四射の値比較で表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 合成同型の端点補正は、明示した中間の等式を共有して各因子へ分配できる。 -/
lemma functorIsoOfEq_trans {X Y : SSet.{u}} {f g h f' g' h' : X ⟶ Y}
    (e : FunctorIso f g) (d : FunctorIso g h) (hf : f = f') (hg : g = g') (hh : h = h') :
    functorIsoOfEq (e ≪≫ d) hf hh = functorIsoOfEq e hf hg ≪≫ functorIsoOfEq d hg hh := by
  subst f' g' h'
  rfl

/-- 持ち上げた二比較の水平合成の下降は、元の二比較の下降の水平合成そのもの。 -/
lemma functorIsoDown_horizontal {A B C : SSet.{u}} [Quasicategory B] [Quasicategory C]
    {f f' : A ⟶ B} {g g' : B ⟶ C}
    (e : FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map f'))
    (d : FunctorIso ((SSet.uliftFunctor.{v, u}).map g) ((SSet.uliftFunctor.{v, u}).map g')) :
    functorIsoDown (functorIsoOfEq
      (e.postcomp ((SSet.uliftFunctor.{v, u}).map g) ≪≫
        d.precomp ((SSet.uliftFunctor.{v, u}).map f'))
      ((SSet.uliftFunctor.{v, u}).map_comp f g).symm
      ((SSet.uliftFunctor.{v, u}).map_comp f' g').symm) =
    (functorIsoDown e).postcomp g ≪≫ (functorIsoDown d).precomp f' := by
  rw [functorIsoOfEq_trans (hg := ((SSet.uliftFunctor.{v, u}).map_comp f' g).symm),
    functorIsoDown_trans, functorIsoDown_postcomp, functorIsoDown_precomp]

end SerrePositivity.InfinityCategories.F2

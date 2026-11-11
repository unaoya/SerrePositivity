module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIso
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の全円柱が同じ二つの指定同型を端点の等式に沿って比較する。
方針：端点の等式を消去し、円柱の外延性と指定辺の類を使う。
規約：代表を選び直さない。使われ方：置換の path と引き戻しの元の path の一致。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：同じ全円柱の指定同型は端点の輸送後に同じ。
方針：円柱の外延性と同型の順方向の射の一致。
規約：指定値。使われ方：元の引き戻し path の同定。 -/
lemma functorIsoOfEq_of_homotopy_h_eq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (H : SSet.Homotopy f g) (H' : SSet.Homotopy f' g')
    (e : FunctorIso f g) (e' : FunctorIso f' g')
    (he : e.hom = SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H))
    (he' : e'.hom = SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H'))
    (hf : f = f') (hg : g = g') (hh : H.h = H'.h) : functorIsoOfEq e hf hg = e' := by
  subst f' g'
  have hH : H = H' := by apply SSet.RelativeMorphism.Homotopy.ext; exact hh
  subst H'
  apply Iso.ext
  exact he.trans he'.symm

/-- 概要：終域だけの等式輸送は元の指定同型と標準同型の合成。
方針：等式を消去。規約：指定値。使われ方：引き戻しの終点の正規化。 -/
lemma functorIsoOfEq_target_trans {X Y : SSet.{u}} {f g g' : X ⟶ Y}
    (e : FunctorIso f g) (hg : g = g') : functorIsoOfEq e rfl hg = e ≪≫ functorEqIso hg := by
  subst g'
  exact (Iso.trans_refl e).symm

end SerrePositivity.InfinityCategories.F2

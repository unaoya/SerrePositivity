module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedSourceComposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedSourceUnit
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor
/-!
概要：出発提示を保持する厳密 dg 作用を、同じ native nerve の作用へ送る。
方針：全 Hom 上で証明した関手等号に dg nerve の厳密関手性を適用する。
規約：dg 関手変数の Hom 複体への作用と表示の閉演算は別途検証する。
使われ方：16時間試作でラベルを再選択しない恒等・合成の高次単体への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Diagnostics
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D E B : Type u)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [DGCategory R E] [DGCategory R B] (κ : Cardinal.{u})

def dgKappaPresentedSourceNativeAction (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R E κ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction R D E κ F)

omit [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [DGCategory R B] in
lemma dgKappaPresentedSourceNativeAction_id :
    dgKappaPresentedSourceNativeAction R D D κ (DGFunctor.id D) =
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedSourceObject R D κ)) := by
  unfold dgKappaPresentedSourceNativeAction
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction_id, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_id]

lemma dgKappaPresentedSourceNativeAction_comp (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R D E) (G : _root_.SerrePositivity.DifferentialGraded.DGFunctor R E B) :
    dgKappaPresentedSourceNativeAction R D E κ F ≫
      dgKappaPresentedSourceNativeAction R E B κ G =
        dgKappaPresentedSourceNativeAction R D B κ (F.comp G) := by
  unfold dgKappaPresentedSourceNativeAction
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedSourceAction_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Diagnostics

module
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceComposition
public import SerrePositivity.InfinityCategories.Derived.DGKappaPresentedSourceUnit
public import SerrePositivity.InfinityCategories.DGNerve.Functor
/-!
概要：出発提示を保持する厳密 dg 作用を、同じ native nerve の作用へ送る。
方針：全 Hom 上で証明した関手等号に dg nerve の厳密関手性を適用する。
規約：dg 関手変数の Hom 複体への作用と表示の閉演算は別途検証する。
使われ方：16時間試作でラベルを再選択しない恒等・合成の高次単体への接続。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D E B : Type u)
  [DGCategory R D] [DGCategory R E] [DGCategory R B] (κ : Cardinal.{u})

def dgKappaPresentedSourceNativeAction (F : DGFunctor R D E) :
    dgNerve R (DGKappaPresentedSourceObject R D κ) ⟶
      dgNerve R (DGKappaPresentedSourceObject R E κ) :=
  dgNerve.map (dgKappaPresentedSourceAction R D E κ F)

omit [DGCategory R E] [DGCategory R B] in
lemma dgKappaPresentedSourceNativeAction_id :
    dgKappaPresentedSourceNativeAction R D D κ (DGFunctor.id D) =
      𝟙 (dgNerve R (DGKappaPresentedSourceObject R D κ)) := by
  unfold dgKappaPresentedSourceNativeAction
  rw [dgKappaPresentedSourceAction_id, dgNerve.map_id]

lemma dgKappaPresentedSourceNativeAction_comp (F : DGFunctor R D E) (G : DGFunctor R E B) :
    dgKappaPresentedSourceNativeAction R D E κ F ≫
      dgKappaPresentedSourceNativeAction R E B κ G =
        dgKappaPresentedSourceNativeAction R D B κ (F.comp G) := by
  unfold dgKappaPresentedSourceNativeAction
  rw [← dgNerve.map_comp, dgKappaPresentedSourceAction_comp]

end SerrePositivity.InfinityCategories

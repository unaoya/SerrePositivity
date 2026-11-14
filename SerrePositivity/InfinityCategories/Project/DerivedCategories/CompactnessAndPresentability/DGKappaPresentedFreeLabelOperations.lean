module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedFreeModel
public import SerrePositivity.DifferentialGraded.Module.ShiftResolution
/-!
概要：ラベル付き κ 未満自由模型の対象作用と整数 shift を与える。
方針：元の表示ラベルへ作用し、shift は対象を変えず次数だけをずらす。
規約：対象作用の恒等・合成・shift との可換性は厳密等式である。
使われ方：16時間試作で全次数作用と閉演算を接続する際のラベル部分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R]
variable {D : Type v} {E : Type w} {B : Type z}
  [DGCategory R D] [DGCategory R E] [DGCategory R B]
  [Small.{u} D] [Small.{u} E] [Small.{u} B] {κ : Cardinal.{u}}

def dgKappaPresentedFreeObjectMap (F : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject E κ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeLabelMap R F X.label⟩

lemma dgKappaPresentedFreeObjectMap_id (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) :
    dgKappaPresentedFreeObjectMap R (DGFunctor.id D) X = X := by
  rcases X with ⟨i⟩
  exact congrArg (fun j : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex D κ =>
    (⟨j⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeLabelMap_id R i)

lemma dgKappaPresentedFreeObjectMap_comp (F : DGFunctor R D E) (G : DGFunctor R E B)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) :
    dgKappaPresentedFreeObjectMap R (F.comp G) X =
      dgKappaPresentedFreeObjectMap R G (dgKappaPresentedFreeObjectMap R F X) := by
  rcases X with ⟨i⟩
  exact congrArg (fun j : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaSphereFreeIndex B κ =>
    (⟨j⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject B κ)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeLabelMap_comp R F G i)

/-- shift は同じ ordinal と対象ラベルを保つ。 -/
def dgKappaPresentedFreeShift (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ :=
  ⟨X.label.1, fun j => ((X.label.2 j).1, (X.label.2 j).2 - s)⟩

lemma dgKappaPresentedFreeObjectMap_shift (F : DGFunctor R D E)
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (s : ℤ) :
    dgKappaPresentedFreeObjectMap R F (dgKappaPresentedFreeShift X s) =
      dgKappaPresentedFreeShift (dgKappaPresentedFreeObjectMap R F X) s := rfl

/-- 同じラベル shift の評価は、元の実加群 shift と同型である。 -/
def dgKappaPresentedFreeShiftIso (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaPresentedFreeObject D κ) (s : ℤ) :
    (ForgetEnrichment.of (Complex R) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ X))⟦s⟧ ≅
      ForgetEnrichment.of (Complex R)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaPresentedFreeValue R D κ (dgKappaPresentedFreeShift X s)) :=
  freeSphereCoproductShiftIso R D
    (fun j : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaSphereFreeCells D X.label =>
      (equivShrink D).symm (X.label.2 j.down).1)
    (fun j => (X.label.2 j.down).2) s

end SerrePositivity.InfinityCategories.Project.DerivedCategories

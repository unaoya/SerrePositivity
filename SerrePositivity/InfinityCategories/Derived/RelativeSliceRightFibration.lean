module
public import SerrePositivity.InfinityCategories.Core.JoinAnodyne
public import SerrePositivity.InfinityCategories.Core.RightFibration
/-!
概要：inner fibration の相対 slice 比較は右ファイブレーション。
方針：右ホーンとの pushout join の inner anodyne 性を、既存の相対 slice 持ち上げに渡す。
規約：全空間と底の quasicategory 性は不要。使われ方：商側三角形への実屋根比較の基底変換。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
/-- inner fibration の相対 slice の全比較は、任意の固定部分図式に対し右ファイブレーション。 -/
instance relativeSliceOverMap_rightFibration {K E B : SSet.{u}}
    (p : K ⟶ E) (r : E ⟶ B) [InnerFibration r] (K₀ : K.Subcomplex) :
    RightFibration (relativeSliceOverMap p K₀.ι r) where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i hi =>
      exact relativeSliceOverMap_hasLiftingProperty K₀ (horn (n + 1) i) r
        (joinUnion_rightHorn_innerAnodyne K₀ n i hi r (InnerFibration.mem (q := r))) p
end SerrePositivity.InfinityCategories

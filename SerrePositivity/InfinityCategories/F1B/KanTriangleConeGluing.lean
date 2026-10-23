module

public import SerrePositivity.InfinityCategories.F1.Joins.CosliceConeExtension
public import SerrePositivity.InfinityCategories.F1.Joins.JoinLeftGluing
public import SerrePositivity.InfinityCategories.Core.JoinPushout

/-!
概要：三角形の最初の二辺の余錐を貼るための join の pushout と終点への相対制限。
方針：標準ホーンの pushout の join による保存と右 anodyne な終点包含を使う。
規約：対象側の図式を固定し、底の余錐を保つ。
使われ方：cocartesian 辺の三角形に沿う消去。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：始点を共有する二辺との join の pushout は最初のホーンとの join。
方針：標準ホーンの pushout に join の左因子の保存定理を適用する。
規約：共通の頂点は両辺の始点。
使われ方：三角形の最初の辺と長辺の余錐の貼り合わせ。 -/
lemma kanJoinLeft_horn₂₀_isPushout (A : SSet.{u}) :
    IsPushout (joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 A))
      (joinMap (stdSimplex.δ (1 : Fin 2)) (𝟙 A))
      (joinMap horn₂₀.ι₀₁ (𝟙 A)) (joinMap horn₂₀.ι₀₂ (𝟙 A)) :=
  join_left_isPushout horn₂₀.isPushout A

/-- 概要：辺の終点への相対 coslice 制限は inner fibration の下で trivial Kan fibration。
方針：終点包含の右 anodyne 性を、その像の部分複体の表示へ移す。
規約：辺自体の cocartesian 性は不要。
使われ方：真ん中の頂点の余錐を三角形の最初の辺へ延長する。 -/
lemma kanRelativeCosliceRestriction_target {X Y : SSet.{u}}
    (e : (Δ[1] : SSet.{u}) ⟶ X) (q : X ⟶ Y) [InnerFibration q] :
    TrivialKanFibration (relativeCosliceRestriction e q (stdSimplex.δ (0 : Fin 2))) := by
  let A := stdSimplex.face (n := 1) {(0 : Fin 2)}ᶜ
  have hA : rightAnodyneExtensions A.ι := by
    rw [← rightAnodyneExtensions.cancel_left_of_respectsIso
      (stdSimplex.faceSingletonComplIso (0 : Fin 2)).hom]
    rw [stdSimplex.faceSingletonComplIso_hom_ι]
    exact endpointInclusion_rightAnodyne
  have := relativeCosliceMap_trivialKanFibration_of_rightAnodyne e q A hA
  have h := relativeCosliceRestriction_trivialKanFibration_subcomplexIso e q A
    (stdSimplex.faceSingletonComplIso (0 : Fin 2))
  simpa only [A, stdSimplex.faceSingletonComplIso_hom_ι] using h

end SerrePositivity.InfinityCategories

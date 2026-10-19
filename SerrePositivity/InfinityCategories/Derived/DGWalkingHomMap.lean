module
public import SerrePositivity.InfinityCategories.Derived.DGWalkingHomEvaluation

/-! # 自由 Hom 係数の鎖写像による変換

概要：係数鎖写像を、二つの対象を厳密に保つ自由 dg 圏の関手へ上げる。
方針：生成辺を係数鎖写像と次の生成辺の合成へ写す。
規約：対象写像は定義上恒等。使われ方：元・商の自由 Hom prism の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded
open scoped ZeroObject
variable (A : Type u) [CommRing A] {M N : Complex A}

/-- 係数鎖写像を二対象 quiver の生成辺の写像にする。 -/
def dgWalkingHomMapEdge (θ : M ⟶ N) : ∀ a b : DGWalkingHomVertex.{v},
    dgWalkingHomQuiver A M a b ⟶ homObject A (DGWalkingHom.{u, v} A N) a b
  | ⟨false⟩, ⟨false⟩ => 0
  | ⟨false⟩, ⟨true⟩ => θ ≫ dgWalkingHomGenerator A N
  | ⟨true⟩, ⟨false⟩ => 0
  | ⟨true⟩, ⟨true⟩ => 0

/-- 係数の鎖写像は、自由 Hom dg 圏の対象を厳密に保つ dg 関手を与える。 -/
def dgWalkingHomMap (θ : M ⟶ N) :
    DGFunctor A (DGWalkingHom.{u, v} A M) (DGWalkingHom.{u, v} A N) :=
  FreeDGCategory.lift A DGWalkingHomVertex (DGWalkingHom A N)
    (dgWalkingHomQuiver A M) (fun x => x) (dgWalkingHomMapEdge A θ)

/-- 自由係数変換の生成辺への作用は元の鎖写像そのもの。 -/
lemma dgWalkingHomMap_generator (θ : M ⟶ N) :
    dgWalkingHomGenerator A M ≫
      (dgWalkingHomMap.{u, v} A θ).map
        (dgWalkingHomSource A M) (dgWalkingHomTarget A M) =
      θ ≫ dgWalkingHomGenerator A N :=
  FreeDGCategory.lift_edge A DGWalkingHomVertex (DGWalkingHom A N)
    (dgWalkingHomQuiver A M) (fun x => x) (dgWalkingHomMapEdge A θ) _ _

end SerrePositivity.InfinityCategories

module

public import SerrePositivity.InfinityCategories.F2.TetrahedronFaceExtension

/-!
概要：三単体の指定比較を元の二面へ制限し、選択済み比較の合成を厳密に保持する。
方針：同じ零頂点を固定した制限先の可縮性から、既存の指定同型を同定する。
規約：比較を再選択しない。使われ方：共有面の比較と三つの合成関係の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (b : (Δ[3] : SSet.{u}) ⊗ A ⟶ B) (v : (Δ[0] : SSet.{u}) ⊗ A ⟶ E)
  (hv : v ≫ p = (scaffoldFirstVertex 3 ▷ A) ≫ b) (j : Fin 4) (hj : j ≠ 0)
local notation "K" => relativeFunctorExtensionSpace p b (scaffoldFirstVertex 3 ▷ A) v hv
local notation "r" => tetrahedronFaceExtensionRestriction p b v hv j hj

/-- 任意の元の指定比較の面への像は、その同じ面の標準比較に厳密に一致する。 -/
lemma tetrahedronFaceExtensionRestriction_vertexIso {x y : K _⦋0⦌} (e : VertexIso x y) :
    VertexIso.map e r =
      (tetrahedronFaceExtensionRestriction_contractible p b v hv j hj).vertexIso
        ((r).app (Opposite.op ⦋0⦌) x) ((r).app (Opposite.op ⦋0⦌) y) :=
  vertexIso_map_eq_contractible
    (tetrahedronFaceExtensionRestriction_contractible p b v hv j hj) e r

/-- 面へ制限した二比較の合成も、同じ直接比較の選択済みの値に等しい。 -/
lemma tetrahedronFaceExtensionRestriction_comparison_trans {x y z : K _⦋0⦌}
    (e : VertexIso x y) (f : VertexIso y z) :
    VertexIso.map e r ≪≫ VertexIso.map f r =
      (tetrahedronFaceExtensionRestriction_contractible p b v hv j hj).vertexIso
        ((r).app (Opposite.op ⦋0⦌) x) ((r).app (Opposite.op ⦋0⦌) z) := by
  rw [← vertexIso_map_trans]
  exact tetrahedronFaceExtensionRestriction_vertexIso p b v hv j hj (e ≪≫ f)

end SerrePositivity.InfinityCategories.F2

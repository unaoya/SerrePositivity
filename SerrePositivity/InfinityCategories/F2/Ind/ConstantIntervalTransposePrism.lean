module

public import SerrePositivity.InfinityCategories.F2.Ind.ConstantIntervalTranspose

/-!
概要：元の全変換の転置から、同じ指定変換の全円柱を回収する。
方針：curry の頂点公式、両端固定 curry の往復、定値変換の prism 公式を使う。
規約：元の全パラメータを保持する厳密な等式。
使われ方：大域密度変換の fiber 作用を同じ元の共同 Hom 変換へ接続する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (A X : SSet.{u}) (x z : X _⦋0⦌)
local notation "T" => intervalMappingSpace (functorVertex (SSet.const x : A ⟶ X))
  (functorVertex (SSet.const z : A ⟶ X))

/-- 同じ転置の指定頂点を区間へ uncurry すると、元の指定変換の全円柱そのもの。 -/
lemma constantIntervalTranspose_uncurry (t : T _⦋0⦌) :
    intervalMappingUncurry ((functorVertexEquiv A _).symm
      ((constantIntervalTranspose A X x z).app (Opposite.op ⦋0⦌) t)) =
        (β_ Δ[1] A).hom ≫
          (simplicialHomotopyOfFunctorEdge (intervalMappingEdgeOfVertex t).toTruncated).h := by
  rw [constantIntervalTranspose, curry_vertex_partial]
  change intervalMappingUncurry ((functorVertexEquiv A _).symm
    ((functorVertexEquiv A _) _)) = _
  rw [Equiv.symm_apply_apply, intervalMappingUncurry_precomp,
    intervalMappingUncurry_curryOfEndpoints]
  have hh : (Δ[1] ◁ lift (𝟙 A) (SSet.const t)) ≫ constantIntervalJointPrism A X x z =
      (β_ Δ[1] A).hom ≫
        lift (𝟙 (A ⊗ (Δ[1] : SSet.{u})))
          (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
        F2.constantTransformationPrism (SSet.yonedaEquiv.symm t) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨s, a⟩
    rfl
  rw [hh, F2.constantTransformationPrism_vertex]
  simp only [lift_fst_assoc, Category.id_comp]

end SerrePositivity.InfinityCategories.F2.Ind

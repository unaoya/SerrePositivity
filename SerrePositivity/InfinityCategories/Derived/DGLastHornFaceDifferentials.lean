module
public import SerrePositivity.InfinityCategories.Derived.DGLastHornCochains
public import SerrePositivity.InfinityCategories.Derived.DGDataTriangleDifferential

/-! # 実最後外ホーンの既知三面の微分式

概要：実ホーンから回収した三点成分の微分式と、最初の辺の閉性を証明する。
方針：既知面への厳密な制限を実三角形の型付き微分式へ渡す。
規約：未知 Q の式を仮定しない。使われ方：既知残差 K の微分と cone の閉成分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]
variable (σ : (Λ[3, 3] : SSet.{max u v}) ⟶ dgNerve A D)

/-- 指定三面の各三点成分は、回収した同じ三辺の合成差を微分に持つ。 -/
lemma dgLastHornKnownFace_differential (j : Fin 4) (hj : j ≠ 3) :
    differential A ((HornData.knownData σ).tripleHom (j.succAbove 0) (j.succAbove 1)
      (j.succAbove 2) (j.succAboveOrderEmb.strictMono (by decide))
        (j.succAboveOrderEmb.strictMono (by decide))) =
      compose A ((HornData.knownData σ).edgeHom (j.succAbove 1) (j.succAbove 2)
        (j.succAboveOrderEmb.strictMono (by decide)))
        ((HornData.knownData σ).edgeHom (j.succAbove 0) (j.succAbove 1)
          (j.succAboveOrderEmb.strictMono (by decide))) (by decide) -
        (HornData.knownData σ).edgeHom (j.succAbove 0) (j.succAbove 2)
          (j.succAboveOrderEmb.strictMono (by decide)) :=
  dgDataTriangle_differential (HornData.knownData σ) (σ.app _ (horn.face 3 j hj))
    j.succAboveOrderEmb.toOrderHom j.succAboveOrderEmb.injective
    (HornData.knownData_pullback_face σ j hj) (j.succAboveOrderEmb.strictMono (by decide))
      (j.succAboveOrderEmb.strictMono (by decide))

/-- 回収した最初の次数零辺も、元の実ホーンの既知二点方程式から閉じている。 -/
lemma dgLastHornFirstEdge_closed :
    differential A ((HornData.knownData σ).edgeHom 0 1 (by decide)) = 0 := by
  have hd := HornData.knownData_equation σ {0, 1} 0 1 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine hd.trans ?_
  unfold SimplexData.rhs
  apply Finset.sum_eq_zero
  intro j _
  have hj : j.val = (0 : Fin 4) ∨ j.val = 1 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using j.property
  rcases hj with h | h
  · simp [h]
  · simp [h]

end SerrePositivity.InfinityCategories

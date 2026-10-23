module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorTrianglePointedLift
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorHomotopyPointedPrism
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.UnstraighteningConstantFamilyMap

/-!
概要：元の指定三角形の第一辺・右辺を、同じ元の普遍 prism の実制限へ厳密に戻す。
方針：指定三角形の二辺の条件を前合成し、元の選択済み作用の一点評価を計算する。
規約：元の実始域射と二つの prism を保持。使われ方：右辺比較の全自然性の適用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B C : SSet.{u + 1}} {F G J : B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d) (s : C ⟶ leftUnstraightening F)
local notation "L" => coherentTransformationTriangleLift F G J (coherentVertexOfHomotopy l)
  (coherentVertexOfHomotopy r) (coherentTriangleOfFunctorTriangle T)
local notation "s₀" => lift s (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "w₀" => unstraighteningMappingFamilyWitness F G
  (SSet.const (coherentVertexOfHomotopy l))
local notation "w₁" => unstraighteningMappingFamilyWitness G J
  (SSet.const (coherentVertexOfHomotopy r))

/-- 元の指定三角形の第一辺は、元の第一変換の同じ普遍 prism の実制限そのもの。 -/
lemma functorTrianglePointedLift_first :
    (Δ[1] ◁ s) ≫ (stdSimplex.δ (2 : Fin 3) ▷ leftUnstraightening F) ≫
      functorTrianglePointedLift T = functorHomotopyPointedPrism l s := by
  calc
    _ = (Δ[1] ◁ s₀) ≫
        ((stdSimplex.δ (2 : Fin 3) ▷ (leftUnstraightening F ⊗ Δ[0])) ≫ (L).prism) := by
      apply SSet.hom_ext
      intro n
      rfl
    _ = (Δ[1] ◁ s₀) ≫ (w₀).toRepresentationWitness.leftPrism :=
      congrArg (fun z => (Δ[1] ◁ s₀) ≫ z) (L).first
    _ = _ := rfl

/-- 元の指定三角形の右辺は、元の第一作用の後の第二変換の同じ普遍 prism。 -/
lemma functorTrianglePointedLift_second :
    (Δ[1] ◁ s) ≫ (stdSimplex.δ (0 : Fin 3) ▷ leftUnstraightening F) ≫
      functorTrianglePointedLift T =
      functorHomotopyPointedPrism r
        (s ≫ (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy l)).val) := by
  have hn : s₀ ≫ lift
      (relativeFunctorUncurry (SSet.const (coherentVertexOfHomotopy l) ≫
        leftUnstraighteningMappingSpaceMap F G)) (snd (leftUnstraightening F) Δ[0]) =
      lift (s ≫ (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy l)).val)
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) := by
    rw [unstraighteningMappingConst_uncurry]
    apply SSet.hom_ext
    intro n
    rfl
  calc
    _ = (Δ[1] ◁ s₀) ≫
        ((stdSimplex.δ (0 : Fin 3) ▷ (leftUnstraightening F ⊗ Δ[0])) ≫ (L).prism) := by
      apply SSet.hom_ext
      intro n
      rfl
    _ = (Δ[1] ◁ s₀) ≫ (Δ[1] ◁ lift
        (relativeFunctorUncurry (SSet.const (coherentVertexOfHomotopy l) ≫
          leftUnstraighteningMappingSpaceMap F G)) (snd (leftUnstraightening F) Δ[0])) ≫
          (w₁).toRepresentationWitness.leftPrism :=
      congrArg (fun z => (Δ[1] ◁ s₀) ≫ z) (L).second
    _ = _ := by
      rw [← Category.assoc, ← whiskerLeft_comp, hn]
      rfl

end SerrePositivity.InfinityCategories.F2

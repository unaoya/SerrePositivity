module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningTransformationFamily

/-!
概要：指定した二つの coherent 変換を、三辺と全三角形を保持して合成する。
方針：全族の三角形充填を一点パラメータへ適用し、長辺の族をその頂点で表示する。
規約：指定された二辺を変更しない。使われ方：元の変換と標的の単位の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：指定した二変換を結ぶ長辺・全三角形・三辺の厳密な制限。
方針：三角形の族をデータとして保持。
規約：二辺は元の指定値。使われ方：単位との合成を後で同じ三角形で照合。 -/
structure CoherentTransformationVertexTriangle {B : SSet.{u + 1}}
    (F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace G J) _⦋0⦌) where
  diagonal : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F J) _⦋0⦌
  diagram : (Δ[2] : SSet.{u + 1}) ⊗ (B ⊗ (Δ[0] : SSet.{u + 1})) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}
  first : (stdSimplex.δ (2 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ diagram =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram (SSet.const x)
  second : (stdSimplex.δ (0 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ diagram =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram (SSet.const y)
  long : (stdSimplex.δ (1 : Fin 3) ▷ (B ⊗ (Δ[0] : SSet.{u + 1}))) ≫ diagram =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyDiagram (SSet.const diagonal)

/-- 概要：元の二変換の合成三角形を全データ付きで選ぶ。
方針：全族の充填と零単体の Yoneda の往復。
規約：元の二辺は厳密に保持。使われ方：指定単位との合成。 -/
def coherentTransformationVertexTriangle {B : SSet.{u + 1}}
    (F G J : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌)
    (y : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace G J) _⦋0⦌) :
    CoherentTransformationVertexTriangle F G J x y := Classical.choice <| by
  obtain ⟨c, H, h₀₁, h₁₂, h₀₂⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentTransformationFamilyTriangle_nonempty
    (SSet.const x : (Δ[0] : SSet.{u + 1}) ⟶ _) (SSet.const y)
  have hc : SSet.const (SSet.yonedaEquiv c) = c :=
    (SSet.yonedaEquiv_symm_zero _).symm.trans (SSet.yonedaEquiv.symm_apply_apply c)
  exact ⟨⟨SSet.yonedaEquiv c, H, h₀₁, h₁₂, by rw [hc]; exact h₀₂⟩⟩

end SerrePositivity.InfinityCategories.Project.FilteredExchange

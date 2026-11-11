module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.SpaceSimplexPointedFamilyRestriction
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.VertexIsoTerminalEquality

/-!
概要：同じ全 pointed 比較の二段の制限は、同じ合成した実制限の比較に一致する。
方針：元の相対前合成の合成則を、同じ指定頂点同型の像へ移す。
規約：実両端と指定比較の値を保持。使われ方：三辺の共有頂点での同時整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 両端の等式による表示変更は、同じ指定同型の像の値を保持する。 -/
lemma vertexIsoOfEq_map_heq {X Y : SSet.{u}} {a b a' b' : X _⦋0⦌}
    (e : VertexIso a b) (ha : a = a') (hb : b = b') (f : X ⟶ Y) :
    HEq (VertexIso.map (vertexIsoOfEq e ha hb) f) (VertexIso.map e f) := by
  subst a' b'
  simp [vertexIsoOfEq]

variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)
local notation "A" => spaceSimplexPointedCoefficients s
local notation "b" => fst Δ[n] A ≫ SSet.yonedaEquiv.symm s
local notation "i" => scaffoldFirstVertex n ▷ A
local notation "v" => snd Δ[0] A ≫
  pointedCoherentFiberComparison (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))) ≫
    vertexFiberι pointedSpaceProjection
      (coherentNerveVertex (EnrichedFunctor.obj s (SimplicialThickening.mk (ULift.up 0))))

/-- 同じ全比較を二段で制限しても、合成した同じ実制限の指定値になる。 -/
lemma spaceSimplexPointedFamilyRestrictionIso_precomp
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v)
    {C D : SSet.{u + 1}} (r : C ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A) (t : D ⟶ C) :
    HEq (VertexIso.map (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ r)
        (relativeFunctorPre pointedSpaceProjection (r ≫ b) t))
      (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ (t ≫ r)) := by
  have hs : HEq
      (VertexIso.map (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ r)
        (relativeFunctorPre pointedSpaceProjection (r ≫ b) t))
      (VertexIso.map
        (VertexIso.map (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
          (relativeFunctorExtensionSpaceι pointedSpaceProjection b i v
            (spaceSimplexPointedFamily_boundary s) ≫ relativeFunctorPre pointedSpaceProjection b r))
        (relativeFunctorPre pointedSpaceProjection (r ≫ b) t)) :=
    vertexIsoOfEq_map_heq _ _ _ _
  rw [vertexIso_map_comp] at hs
  have hm := vertexIso_map_heq (spaceSimplexPointedFamilyComparisonIso s L hL hL₀)
    (show (relativeFunctorExtensionSpaceι pointedSpaceProjection b i v
      (spaceSimplexPointedFamily_boundary s) ≫ relativeFunctorPre pointedSpaceProjection b r) ≫
      relativeFunctorPre pointedSpaceProjection (r ≫ b) t =
      relativeFunctorExtensionSpaceι pointedSpaceProjection b i v
        (spaceSimplexPointedFamily_boundary s) ≫
          relativeFunctorPre pointedSpaceProjection b (t ≫ r) by
      rw [Category.assoc, relativeFunctorPre_comp])
  exact hs.trans (hm.trans (spaceSimplexPointedFamilyRestrictionIso_heq s L hL hL₀ _).symm)

/-- 等しい実制限射なら、制限した同じ指定比較も値と型を含めて一致する。 -/
lemma spaceSimplexPointedFamilyRestrictionIso_congr
    (L : (Δ[n] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u})
    (hL : L ≫ pointedSpaceProjection = b) (hL₀ : i ≫ L = v)
    {C : SSet.{u + 1}} {r r' : C ⟶ (Δ[n] : SSet.{u + 1}) ⊗ A} (h : r = r') :
    HEq (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ r)
      (spaceSimplexPointedFamilyRestrictionIso s L hL hL₀ r') := by
  subst r'
  rfl

end SerrePositivity.InfinityCategories.F2

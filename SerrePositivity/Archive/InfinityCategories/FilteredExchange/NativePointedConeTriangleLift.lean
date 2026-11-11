module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.NativePointedConeLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeTriangle

/-!
概要：始点固定の全 pointed 錐を、その元の native な三角形へ制限する。
方針：三角形包含が錐の頂点を保つ式を使い、全持ち上げを厳密に制限する。
規約：全二単体・始点・全パラメータを保持。使われ方：既存の二三角形との比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- native 三角形の包含は最初の頂点を元の錐の頂点へ厳密に写す。 -/
lemma coneTriangleInclusion_firstVertex {K : SSet.{u}} (e : (Δ[1] : SSet.{u}) ⟶ K) :
    scaffoldFirstVertex 2 ≫ coneTriangleInclusion e = joinInl Δ[0] K := by
  unfold scaffoldFirstVertex coneTriangleInclusion
  rw [← joinStdSimplexIso_inl_vertex 1]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, joinInl_joinMap, Category.id_comp]

variable {K A : SSet.{u + 1}} {d : K ⟶ SpaceInfinity.{u}} (c : JoinCone d)
  (s : A ⟶ PointedSpaceInfinity.{u}) (hs : s ≫ pointedSpaceProjection = SSet.const c.vertex)
  (k : K _⦋1⦌)
local notation "j" => coneTriangleInclusion (SSet.yonedaEquiv.symm k)
local notation "D" => SSet.yonedaEquiv.symm (nativeConeTriangle c k)
local notation "i" => scaffoldFirstVertex 2 ▷ A
local notation "v" => snd Δ[0] A ≫ s

/-- 同じ全 pointed 錐の三角形への制限。 -/
def nativePointedConeTriangleLift : (Δ[2] : SSet.{u + 1}) ⊗ A ⟶ PointedSpaceInfinity.{u} :=
  (j ▷ A) ≫ nativePointedConeLift c s hs

/-- 底は元の native 錐の同じ二単体である。 -/
lemma nativePointedConeTriangleLift_projection :
    nativePointedConeTriangleLift c s hs k ≫ pointedSpaceProjection = fst Δ[2] A ≫ D := by
  rw [nativePointedConeTriangleLift, Category.assoc, nativePointedConeLift_projection,
    ← Category.assoc, whiskerRight_fst, Category.assoc]
  rw [nativeConeTriangle, Equiv.symm_apply_apply]

/-- 全錐の左右三角形は同じ元の始点族を保つ。 -/
lemma nativePointedConeTriangleLift_initial : i ≫ nativePointedConeTriangleLift c s hs k = v := by
  rw [nativePointedConeTriangleLift, ← Category.assoc, ← comp_whiskerRight,
    coneTriangleInclusion_firstVertex]
  exact nativePointedConeLift_initial c s hs

include hs in
/-- 同じ始点族は、三角形図式の最初の頂点の制限を被覆する。 -/
lemma nativePointedConeTriangle_initial : v ≫ pointedSpaceProjection = i ≫ (fst Δ[2] A ≫ D) := by
  rw [← nativePointedConeTriangleLift_initial c s hs k, Category.assoc,
    nativePointedConeTriangleLift_projection]

end SerrePositivity.InfinityCategories.F2

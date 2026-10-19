module

public import SerrePositivity.InfinityCategories.HomotopyLimits.JoinAssociatorInclusions
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentConeSections

/-!
概要：coherent な錐そのものの図式上に、その頂点を始点とする標準の coslice 切断を作る。
方針：二つの左頂点を潰す join の射を構成し、元の錐を再び curry する。
規約：元の錐の quasicategory 性・極限性を要求しない。
使われ方：HTT 4.2.4.1 の錐全体上の豊穣 Hom の族の延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 二つの左頂点を一点へ潰す射。 -/
def coneIdentityFold : join (Δ[0] : SSet.{u}) Δ[0] ⟶ Δ[0] :=
  stdSimplex.isTerminalObj₀.from _

/-- 錐の形にもう一度前置した頂点を、元の錐の頂点へ潰す射。 -/
def coneIdentityCollapse (K : SSet.{u}) :
    join (Δ[0] : SSet.{u}) (join Δ[0] K) ⟶ join Δ[0] K :=
  (joinAssociator Δ[0] Δ[0] K).inv ≫ joinMap coneIdentityFold (𝟙 K)

/-- 元の錐の形への右包含に沿って潰すと恒等射になる。 -/
lemma coneIdentityCollapse_right (K : SSet.{u}) :
    joinInr (Δ[0] : SSet.{u}) (join Δ[0] K) ≫ coneIdentityCollapse K = 𝟙 _ := by
  rw [coneIdentityCollapse, ← Category.assoc, joinAssociator_inv_rightPair, ← joinMap_comp]
  have h : joinInr (Δ[0] : SSet.{u}) Δ[0] ≫ coneIdentityFold = 𝟙 _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, Category.id_comp, joinMap_id]

/-- 新しい左頂点は元の錐の左頂点に写る。 -/
lemma coneIdentityCollapse_left (K : SSet.{u}) :
    joinInl (Δ[0] : SSet.{u}) (join Δ[0] K) ≫ coneIdentityCollapse K =
      joinInl Δ[0] K := by
  rw [coneIdentityCollapse, ← Category.assoc, joinAssociator_inv_first, Category.assoc,
    joinInl_joinMap, ← Category.assoc]
  have h : joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ coneIdentityFold = 𝟙 _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, Category.id_comp]

/-- 元の図式に沿って錐を前置してから潰すと、元の錐の形の恒等射になる。 -/
lemma coneIdentityCollapse_outer (K : SSet.{u}) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (joinInr Δ[0] K) ≫ coneIdentityCollapse K = 𝟙 _ := by
  rw [coneIdentityCollapse, ← Category.assoc, joinAssociator_inv_outerPair, ← joinMap_comp]
  have h : joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ coneIdentityFold = 𝟙 _ :=
    stdSimplex.isTerminalObj₀.hom_ext _ _
  rw [h, Category.id_comp, joinMap_id]

variable {K X : SSet.{u}} {p : K ⟶ X}

/-- 錐の図式全体上の、元の頂点を始点とする標準 coslice 切断。 -/
def coneIdentityCosliceSection (c : JoinCone p) :
    join (Δ[0] : SSet.{u}) K ⟶ sliceUnder (SSet.yonedaEquiv.symm c.vertex) :=
  sliceUnderCurry (coneIdentityCollapse K ≫ c.val) (by
    rw [← Category.assoc, coneIdentityCollapse_left, coherentCone_inl_vertex])

/-- 標準 coslice 切断は錐そのものの図式を厳密に被覆する。 -/
lemma coneIdentityCosliceSection_projection (c : JoinCone p) :
    coneIdentityCosliceSection c ≫ sliceUnderProjection (SSet.yonedaEquiv.symm c.vertex) =
      c.val := by
  rw [coneIdentityCosliceSection, sliceUnderCurry_projection, ← Category.assoc,
    coneIdentityCollapse_right, Category.id_comp]

/-- 錐全体の標準切断を元の図式へ制限すると、元の錐の coslice 表示に一致する。 -/
lemma coneIdentityCosliceSection_restrict (c : JoinCone p) :
    joinInr (Δ[0] : SSet.{u}) K ≫ coneIdentityCosliceSection c =
      coherentConeCosliceSection c := by
  apply sliceUnderUncurry_injective (SSet.yonedaEquiv.symm c.vertex)
  rw [sliceUnderUncurry_precomp, coneIdentityCosliceSection, sliceUnderUncurry_curry,
    ← Category.assoc, coneIdentityCollapse_outer]
  rw [Category.id_comp, coherentConeCosliceSection, sliceUnderUncurry_curry]

end
end SerrePositivity.InfinityCategories.HomotopyLimits

module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ConeIdentitySection

/-!
概要：錐全体の標準 coslice 切断の頂点での値を、恒等射の coslice 点と同定する。
方針：join の前二因子の面に沿って、二つの頂点の collapse を計算する。
規約：任意の単体集合と coherent な錐を扱い、充填性を要求しない。
使われ方：明示的な錐全体の Hom の族の頂点条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 前二頂点の面への collapse は、その二頂点を元の頂点へ潰す射。 -/
lemma coneIdentityCollapse_apex (K : SSet.{u}) :
    joinMap (𝟙 (Δ[0] : SSet.{u})) (joinInl Δ[0] K) ≫ coneIdentityCollapse K =
      coneIdentityFold ≫ joinInl Δ[0] K := by
  rw [coneIdentityCollapse, ← Category.assoc, joinAssociator_inv_leftPair,
    joinInl_joinMap]

/-- 一点の恒等射を、二頂点を潰す射で coslice の零単体として表示する。 -/
def cosliceIdentityPoint {X : SSet.{u}} (z : X _⦋0⦌) :
    Δ[0] ⟶ sliceUnder (SSet.yonedaEquiv.symm z) :=
  sliceUnderCurry (coneIdentityFold ≫ SSet.yonedaEquiv.symm z) (by
    have h : joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ coneIdentityFold = 𝟙 _ :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [← Category.assoc, h, Category.id_comp])

/-- 錐全体の標準切断の頂点制限は、頂点の恒等射の coslice 点である。 -/
lemma coneIdentityCosliceSection_apex {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) :
    joinInl (Δ[0] : SSet.{u}) K ≫ coneIdentityCosliceSection c =
      cosliceIdentityPoint c.vertex := by
  apply sliceUnderUncurry_injective (SSet.yonedaEquiv.symm c.vertex)
  rw [sliceUnderUncurry_precomp, coneIdentityCosliceSection, sliceUnderUncurry_curry,
    ← Category.assoc, coneIdentityCollapse_apex, Category.assoc,
    coherentCone_inl_vertex, cosliceIdentityPoint, sliceUnderUncurry_curry]

end
end SerrePositivity.InfinityCategories.HomotopyLimits

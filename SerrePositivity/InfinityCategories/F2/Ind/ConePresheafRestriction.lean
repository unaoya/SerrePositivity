module

public import SerrePositivity.InfinityCategories.F1.PresheafPointwiseColimits
public import SerrePositivity.InfinityCategories.F1.RepresentablePresheafAllSmallLimits
public import SerrePositivity.InfinityCategories.F2.FunctorCoconeReindex
public import SerrePositivity.InfinityCategories.F2.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.F2.LimitConeFamilyReadback

/-!
概要：元の小さい全錐に前層を制限し、同じ全錐の空間値族を作る。
方針：宇宙を持ち上げた全錐への前合成と関手頂点の往復を使う。
規約：底図式だけでなく元の全錐を保持する。
使われ方：有限極限交換による Ind 前層の有限余極限の反変保存性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {K C : SSet.{u}} {D : K ⟶ C.op} (c : JoinCone D)

/-- 元の全錐への制限を、全前層の関手空間上で同時に行う。 -/
def conePresheafRestriction : PresheafInfinity C ⟶
    (ihom (join (Δ[0] : SSet.{u + 1}) ((SSet.uliftFunctor.{u + 1, u}).obj K))).obj
      SpaceInfinity.{u} :=
  (pre (JoinCone.ulift.{u, u + 1} c).val).app SpaceInfinity.{u}

/-- 制限族の読み戻しは元の全錐に同じ前層を後合成した錐そのもの。 -/
lemma conePresheafRestriction_isLimit_iff
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) :
    IsLimitCone (functorVertexCone
      ((conePresheafRestriction c).app (Opposite.op ⦋0⦌) (functorVertex F))) ↔
      IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} c)) := by
  apply isLimitCone_functorVertexCone_iff_of_val
  change (functorVertexEquiv _ _).symm
    (((pre (JoinCone.ulift.{u, u + 1} c).val).app SpaceInfinity).app _ (functorVertex F)) = _
  rw [functorVertexMap_precomp]
  have hF : (functorVertexEquiv _ _).symm (functorVertex F) = F :=
    (functorVertexEquiv _ _).symm_apply_apply F
  rw [hF]
  rfl

/-- 元の前層余極限の同じ全錐への制限は、全錐上で点ごとの余極限。 -/
lemma conePresheafRestriction_isPointwiseColimit
    {B : SSet.{u}} (p : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ PresheafInfinity C)
    (d : JoinCocone p) (hd : IsColimitCone d) :
    IsPointwiseColimitCone (mapJoinCocone (conePresheafRestriction c) d) := by
  have hp : IsPointwiseColimitCone d := by
    rintro ⟨k⟩
    obtain ⟨x, rfl⟩ := SSet.opObjEquiv.symm.surjective k
    exact presheafInfinity_evaluation_isColimit p d hd x
  exact hp.reindex (JoinCone.ulift.{u, u + 1} c).val

end SerrePositivity.InfinityCategories.F2.Ind

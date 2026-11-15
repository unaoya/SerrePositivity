module
public import SerrePositivity.EInfinity.HomotopyWeight.ProjectiveHornValues

/-!
概要：同じ重みの射を自由ホーンで分解し、元のcofibrancyと各値の性質を記録する。
方針：既存の小対象分解を選び、自由評価随伴でその二つの持ち上げ条件を読む。
規約：IS-W2 R03a.1の証明分割。重みの射と分解の等式を保つ。
使われ方：重みの成分ごとの弱同値を、制限の二種類のホモトピー同値へ分ける。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.HomotopyWeight
open CategoryTheory Limits SSet HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
variable (I : Type u) [SmallCategory I]

/-- 自由ホーンの左類は、同じ図式圏の自由境界の左類に入る。 -/
theorem projectiveHorn_cofibration {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hj : (horns I).rlp.llp j) : (boundaries I).rlp.llp j := by
  intro F G p hp
  apply hj
  rw [horns_rlp]
  intro i X Y f hf
  have hm : Mono f := SSet.modelCategoryQuillen.J_le_monomorphisms _ hf
  exact SSet.rlp_monomorphisms.ge _ ((boundaries_rlp I).le _ hp i) f hm

/-- 同じ元の重みの射の自由ホーンによる実際の小対象分解。 -/
def projectiveHornFactorization {V W : I ⥤ SSet.{u}} (j : V ⟶ W) :
    MorphismProperty.MapFactorizationData (horns I).rlp.llp (horns I).rlp j :=
  MorphismProperty.factorizationData _ _ _

/-- 同じ小対象分解の左射は、元の各値でanodyne。 -/
theorem projectiveHornFactorization_i_anodyne {V W : I ⥤ SSet.{u}} (j : V ⟶ W) (i : I) :
    SSet.anodyneExtensions ((projectiveHornFactorization I j).i.app i) :=
  projectiveHorn_anodyne I _ (projectiveHornFactorization I j).hi i

/-- 同じ小対象分解の右射は、元の各値でKan fibration。 -/
theorem projectiveHornFactorization_p_fibration {V W : I ⥤ SSet.{u}} (j : V ⟶ W) (i : I) :
    Fibration ((projectiveHornFactorization I j).p.app i) :=
  (SSet.modelCategoryQuillen.fibration_iff _).mpr
    ((horns_rlp I).le _ (projectiveHornFactorization I j).hp i)

/-- 元の始域が射影cofibrantなら、同じ小対象分解の中間重みもそうである。 -/
theorem projectiveHornFactorization_cofibrant {V W : I ⥤ SSet.{u}} (j : V ⟶ W)
    (hV : (boundaries I).rlp.llp (initial.to V)) :
    (boundaries I).rlp.llp (initial.to (projectiveHornFactorization I j).Z) := by
  have hc := (boundaries I).rlp.llp.comp_mem _ _ hV
    (projectiveHorn_cofibration I _ (projectiveHornFactorization I j).hi)
  have he : initial.to V ≫ (projectiveHornFactorization I j).i =
      initial.to (projectiveHornFactorization I j).Z := initial.hom_ext _ _
  exact he ▸ hc

end SerrePositivity.EInfinity.HomotopyWeight

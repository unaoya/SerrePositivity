module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConePrecomp
public import SerrePositivity.KST.SConstruction.DGModuleNaturalConeRotationInv

/-!
概要：元自然 cone 包含の全前合成と全入力移送を保持する。
方針：元閉成分の前合成回収と入力等号の消去を抽象的な関手で検査する。
規約：元全包含を置換せず、検証上限を変更しない。
使われ方：元実逆回転包含の元始域への制限。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)

/-- 概要：元自然 cone 包含の前合成は同じ前合成 cone の包含。
方針：元全 cone の前合成等号と元閉成分の回収を使う。
規約：全厳密比較の型付き一致。使われ方：元始域上の同じ包含の回収。 -/
lemma dgModuleNaturalConeInr_precomp_heq {Q : Type z} [DGCategory R Q]
    (H : DGFunctor R Q P) :
    HEq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H (dgModuleNaturalConeInr R D F G η))
      (dgModuleNaturalConeInr R D (H.comp F) (H.comp G) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H η)) := by
  apply dgModuleStrictNatTrans_heq_of_arrow_heq R D _ _ _ _ _
    (dgModuleNaturalConeInr R D (H.comp F) (H.comp G) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H η))
    rfl (dgModuleNaturalConeFunctor_precomp R D F G η H)
  intro x
  have hi := dgModuleNaturalConeInr_arrow R D F G η (H.obj x)
  have hl := dgModuleNaturalConeInr_arrow R D (H.comp F) (H.comp G)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H η) x
  exact heq_of_eq (hi.trans hl.symm)

/-- 概要：元二軸と元入力比較の同じ移送は同じ自然 cone 包含を保つ。
方針：元全入力等号を消去する。
規約：元包含の型付き一致。使われ方：実逆回転全族の同じ包含への端点回収。 -/
lemma dgModuleNaturalConeInr_heq
    (F' G' : DGFunctor R P (RightModule R D)) (η' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')
    (hF : F = F') (hG : G = G') (hη : HEq η η') :
    HEq (dgModuleNaturalConeInr R D F G η) (dgModuleNaturalConeInr R D F' G' η') := by
  cases hF
  cases hG
  cases eq_of_heq hη
  rfl
end SerrePositivity.KST.SConstruction

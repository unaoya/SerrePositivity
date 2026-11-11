module
public import SerrePositivity.KST.SConstruction.DGModuleNaturalCone
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleExtensionYonedaStrict
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStrictNatTransTransport

/-!
概要：元実 cone の全関手族を元入力への前合成で保持する。
方針：元二つの Hom 作用と零第三成分を同じ前合成で回収する。
規約：元実 cone・全 Hom・元全厳密比較を保持する。
使われ方：実逆回転の全小模型比較を元始域上の同じ cone 入力へ接続する。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {P : Type w} [DGCategory R P]
  (F G : DGFunctor R P (RightModule R D)) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)

/-- 概要：元全比較の前合成は元閉成分の同じ対象評価。
方針：元全厳密前合成の成分定義を回収する。
規約：元実閉射の等号。使われ方：元 cone 入力の全前合成照合。 -/
lemma dgModuleNaturalConeArrow_precomp {Q : Type z} [DGCategory R Q]
    (H : DGFunctor R Q P) (x : Q) :
    dgModuleNaturalConeArrow R D (H.comp F) (H.comp G) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H η) x =
      dgModuleNaturalConeArrow R D F G η (H.obj x) := rfl

/-- 概要：元実 cone 全関手への前合成は同じ前合成全比較の実 cone 全関手。
方針：元全 Hom 写像の各次数で同じ二成分と零第三成分を回収する。
規約：元全関手の等号。使われ方：実逆回転小模型の元始域への制限。 -/
lemma dgModuleNaturalConeFunctor_precomp {Q : Type z} [DGCategory R Q]
    (H : DGFunctor R Q P) :
    H.comp (dgModuleNaturalConeFunctor R D F G η) =
      dgModuleNaturalConeFunctor R D (H.comp F) (H.comp G) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H η) := by
  apply EnrichedFunctor.ext (Complex R)
    (F := H.comp (dgModuleNaturalConeFunctor R D F G η))
    (G := dgModuleNaturalConeFunctor R D (H.comp F) (H.comp G) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H η))
    (fun _ => rfl)
  intro x y
  change (H.map x y ≫ dgModuleNaturalConeHomMap R D F G η (H.obj x) (H.obj y)) ≫ 𝟙 _ =
    dgModuleNaturalConeHomMap R D (H.comp F) (H.comp G) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp H η) x y
  rw [Category.comp_id]
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- 概要：同じ二軸と元全比較の型付き一致は元実 cone 全族の等号を与える。
方針：二軸の等号と全厳密比較の型付き一致に等号帰納を使う。
規約：対象別の同値へ弱めない。使われ方：元実逆回転 cone 全入力の回収。 -/
lemma dgModuleNaturalConeFunctor_eq_of_heq
    (F' G' : DGFunctor R P (RightModule R D)) (η' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')
    (hF : F = F') (hG : G = G') (hη : HEq η η') :
    dgModuleNaturalConeFunctor R D F G η = dgModuleNaturalConeFunctor R D F' G' η' := by
  cases hF
  cases hG
  cases eq_of_heq hη
  rfl
/-- 概要：元二軸と元閉射の型付き一致は元全厳密比較の一致を与える。
方針：二軸を等号帰納し閉射・閉元対応の逆律で全成分を照合する。
規約：全厳密自然性を保持。使われ方：同じ実 cone 入力の回収。 -/
lemma dgModuleStrictNatTrans_heq_of_arrow_heq
    (F' G' : DGFunctor R P (RightModule R D)) (η' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')
    (hF : F = F') (hG : G = G')
    (ha : ∀ x, HEq (dgModuleNaturalConeArrow R D F G η x)
      (dgModuleNaturalConeArrow R D F' G' η' x)) : HEq η η' := by
  subst F' G'
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_heq_of_val η η' rfl rfl
  intro x
  apply heq_of_eq
  exact (dgModuleNaturalConeArrow_cycle R D F G η x).symm.trans
    ((congrArg (fun f => (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val)
      (eq_of_heq (ha x))).trans (dgModuleNaturalConeArrow_cycle R D F G η' x))

end SerrePositivity.KST.SConstruction

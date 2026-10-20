module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ParameterUnitHom
public import SerrePositivity.InfinityCategories.HomotopyLimits.QuasicategoryParameter
public import SerrePositivity.InfinityCategories.F1B.UnitMappingAdjunction

/-!
概要：任意の単体集合パラメータ上の標準単位 Hom 対応を全単射へ強める。
方針：inner anodyne な制限の充満忠実性と、元の単位の式の自然性を使う。
規約：native な錐の極限性への接続は別工程。使われ方：一般 coherent 極限の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 標準単位の写像空間条件から、任意の単体集合パラメータ上の標準 Hom 全単射を得る。 -/
lemma parameterUnitHomMap_bijective {A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (η : FunctorHom (𝟙 X) (F ≫ G)) (hη : UnitMappingSpaceCondition η)
    (U : A ⟶ X) (V : A ⟶ Y) : Function.Bijective (parameterUnitHomMap η U V) := by
  obtain ⟨B, k, U', V', hk, hB, hU, hV⟩ := exists_quasicategory_common_parameter U V
  have : Quasicategory B := hB
  have hs := functorHomPrecomp_bijective_of_innerAnodyne k hk (U' ≫ F) V'
  have ht := functorHomPrecomp_bijective_of_innerAnodyne k hk U' (V' ≫ G)
  have hb : Function.Bijective (parameterUnitHomMap η U' V') := by
    have he : parameterUnitHomMap η U' V' = qcatUnitHomMap η U' V' := by
      funext α
      exact parameterUnitHomMap_eq η U' V' α
    rw [he]
    exact hη.qcatUnitHomMap_bijective U' V'
  subst U V
  constructor
  · intro α β he
    obtain ⟨α', rfl⟩ := hs.surjective α
    obtain ⟨β', rfl⟩ := hs.surjective β
    rw [parameterUnitHomMap_precomp, parameterUnitHomMap_precomp] at he
    have h := hb.injective (ht.injective he)
    subst β'
    rfl
  · intro β
    obtain ⟨β', rfl⟩ := ht.surjective β
    obtain ⟨α', hα'⟩ := hb.surjective β'
    refine ⟨(hoFunctor.map ((pre k).app Y)).toFunctor.map α', ?_⟩
    rw [parameterUnitHomMap_precomp, hα']

/-- 元の指定単位による標準の Hom 対応。任意の単体集合パラメータで使える。 -/
def parameterUnitHomEquiv {A X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (hη : UnitMappingSpaceCondition η) (U : A ⟶ X) (V : A ⟶ Y) :
    FunctorHom (U ≫ F) V ≃ FunctorHom U (V ≫ G) :=
  Equiv.ofBijective (parameterUnitHomMap η U V) (parameterUnitHomMap_bijective η hη U V)

end
end SerrePositivity.InfinityCategories.HomotopyLimits

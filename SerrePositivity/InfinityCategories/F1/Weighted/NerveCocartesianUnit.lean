module

public import SerrePositivity.InfinityCategories.F1.Weighted.NerveCocartesianScaffold
public import SerrePositivity.InfinityCategories.F1.Weighted.NerveTransportUnit
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianSectionFamilies

/-!
概要：係数図式から weighted nerve の cocartesian strict transport への自然な比較。
方針：taut scaffold の under 評価を cocartesian section の族へ curry する。
規約：係数値は quasicategory。全次数の同じ比較を元の section 空間へ含めて照合する。
使われ方：Cat∞ 値 straightening と unstraightening の strict 図式での比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- under 評価で係数の頂点を固定した各辺は最後の係数が可逆となる。 -/
lemma tautScaffold_underEvaluation_isCocartesian {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] (c : C)
    (x : (F.obj c) _⦋0⦌) (e : (nerve (Under c)) _⦋1⦌) :
    IsCocartesianEdge (weightedNerveProjection F)
      ((simplicialReplacementUnderEvaluation F c ≫ tautScaffold F).app _
        (e, PinchedHom.constant x 1)) := by
  apply isCocartesianEdge_weightedNerve_of_coefficient
  change IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv
    (stdSimplex.map (simplexPrefixInclusion 1 1 _) ≫
      (SSet.yonedaEquiv.symm (PinchedHom.constant x 1) ≫ F.map (e.obj 0).hom) ≫
      F.map ((e ⋙ Under.forget c).map (homOfLE (Fin.zero_le (Fin.last 1)))))))
  rw [simplexPrefixInclusion_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hx : SSet.yonedaEquiv.symm (PinchedHom.constant x 1) = SSet.const x := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv.apply_symm_apply]
    rfl
  rw [hx, SSet.const_comp, SSet.const_comp]
  exact isInvertibleEdge_map_const _ 0

/-- 係数の値を、同じ taut scaffold が定める cocartesian section の族へ写す。 -/
def weightedNerveCocartesianUnitComponent {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] (c : C) :
    F.obj c ⟶ SerrePositivity.InfinityCategories.cocartesianStrictTransport (weightedNerveProjection F) c :=
  SerrePositivity.InfinityCategories.cocartesianSectionsCurry
    (simplicialReplacementUnderEvaluation F c ≫ tautScaffold F) (by
      rw [Category.assoc, tautScaffold_projection,
        simplicialReplacementUnderEvaluation_projection])
    (tautScaffold_underEvaluation_isCocartesian F c)

/-- cocartesian section の包含後には、既存の標準単位の全次数の射と一致する。 -/
lemma weightedNerveCocartesianUnitComponent_ι {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] (c : C) :
    weightedNerveCocartesianUnitComponent F c ≫
      SerrePositivity.InfinityCategories.cocartesianSectionsι (weightedNerveProjection F) (nerveMap (Under.forget c)) =
        (weightedNerveTransportUnit F).app c := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro τ
  exact (weightedNerveTransportUnit_app F c n m x α τ).symm

/-- 元の係数図式から cocartesian strict transport への図式全体の自然変換。 -/
def weightedNerveCocartesianTransportUnit {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] :
    F ⟶ SerrePositivity.InfinityCategories.cocartesianStrictTransportDiagram (weightedNerveProjection F) where
  app := weightedNerveCocartesianUnitComponent F
  naturality c d f := by
    apply (cancel_mono
      (SerrePositivity.InfinityCategories.cocartesianSectionsι (weightedNerveProjection F) (nerveMap (Under.forget d)))).1
    rw [Category.assoc, weightedNerveCocartesianUnitComponent_ι]
    let i : Over.mk (nerveMap (Under.forget d)) ⟶
        Over.mk (nerveMap (Under.forget c)) :=
      Over.homMk (nerveUnderMap f) (nerveUnderMap_projection f)
    have hpre := SerrePositivity.InfinityCategories.cocartesianSectionsPre_ι (weightedNerveProjection F) i
    change SerrePositivity.InfinityCategories.cocartesianSectionsPre (weightedNerveProjection F) i ≫
        SerrePositivity.InfinityCategories.cocartesianSectionsι (weightedNerveProjection F) (nerveMap (Under.forget d)) =
      SerrePositivity.InfinityCategories.cocartesianSectionsι (weightedNerveProjection F) (nerveMap (Under.forget c)) ≫
        (leftStrictTransportDiagram (weightedNerveProjection F)).map f at hpre
    calc
      _ = (weightedNerveTransportUnit F).app c ≫
          (leftStrictTransportDiagram (weightedNerveProjection F)).map f :=
        (weightedNerveTransportUnit F).naturality f
      _ = (weightedNerveCocartesianUnitComponent F c ≫
          SerrePositivity.InfinityCategories.cocartesianSectionsι (weightedNerveProjection F) (nerveMap (Under.forget c))) ≫
          (leftStrictTransportDiagram (weightedNerveProjection F)).map f := by
        rw [weightedNerveCocartesianUnitComponent_ι]
      _ = weightedNerveCocartesianUnitComponent F c ≫
          (SerrePositivity.InfinityCategories.cocartesianSectionsPre (weightedNerveProjection F) i ≫
            SerrePositivity.InfinityCategories.cocartesianSectionsι (weightedNerveProjection F) (nerveMap (Under.forget d))) := by
        rw [Category.assoc, hpre]
      _ = _ := (Category.assoc _ _ _).symm

/-- cocartesian 比較を恒等射で評価すると元の標準 fiber 同型となる。 -/
lemma weightedNerveCocartesianTransportUnit_evaluate {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] (c : C) :
    (weightedNerveCocartesianTransportUnit F).app c ≫
      SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate (weightedNerveProjection F) c =
        weightedNerveFiberMap F c := by
  change weightedNerveCocartesianUnitComponent F c ≫
    (SerrePositivity.InfinityCategories.cocartesianSectionsι (weightedNerveProjection F) (nerveMap (Under.forget c)) ≫ _) = _
  rw [← Category.assoc, weightedNerveCocartesianUnitComponent_ι]
  exact weightedNerveTransportUnit_evaluate F c

/-- 同じ図式全体の cocartesian 比較は各対象で ∞ 圏の同値。 -/
lemma weightedNerveCocartesianTransportUnit_isQCatEquivalence {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) [∀ c, Quasicategory (F.obj c)] (c : C) :
    IsQCatEquivalence ((weightedNerveCocartesianTransportUnit F).app c) := by
  apply (SerrePositivity.InfinityCategories.cocartesianStrictTransportEvaluate_isQCatEquivalence
    (weightedNerveProjection F) c).cancel_right
  rw [weightedNerveCocartesianTransportUnit_evaluate]
  exact (qCatEquivalenceOfIso (weightedNerveFiberIso F c)).isQCatEquivalence

end SerrePositivity.InfinityCategories

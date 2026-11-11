module

public import SerrePositivity.KST.Spectra.D3GradedCompositionNerve
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom

/-!
概要：厳密豊穣変換の前後合成を、同じ coherent な区間族の前後合成と照合する。
方針：順序付き円柱の元の Hom を保つ基底関手を作り、円柱の作用を全単体で比較する。
規約：指定された変換の値と端点を保持する。点別比較からは推論しない。
使われ方：右射影の構造正方形の実現を、既存の段関手同型の前後合成へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra
variable {C D E : Type v} [Category.{u} C] [Category.{u} D] [Category.{u} E]
  [SimplicialCategory C] [SimplicialCategory D] [SimplicialCategory E]

/-- 順序の証明を固定し、元の豊穣 Hom へ同じ基底関手を作用させる。 -/
def d3OrderedCylinderMap (K : EnrichedFunctor SSet.{u} C D) (m : ℕ) :
    EnrichedFunctor SSet.{u} (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin (m + 1)) C)
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedOrderedCylinder.Object (Fin (m + 1)) D) where
  obj X := ⟨X.position, K.obj X.val⟩
  map X Y := {
    app d := ↾fun ⟨p, f⟩ ↦ (p, (K.map X.val Y.val).app d f)
    naturality {d e} α := by
      apply ConcreteCategory.hom_ext
      rintro ⟨p, f⟩
      change (p, (K.map X.val Y.val).app e ((X.val ⟶[SSet] Y.val).map α f)) =
        (p, (K.obj X.val ⟶[SSet] K.obj Y.val).map α ((K.map X.val Y.val).app d f))
      exact Prod.ext rfl (ConcreteCategory.congr_hom ((K.map X.val Y.val).naturality α) f) }
  map_id X := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟩
    apply Prod.ext
    · rfl
    · change (K.map X.val X.val).app d ((eId SSet X.val).app d PUnit.unit) =
        (eId SSet (K.obj X.val)).app d PUnit.unit
      exact ConcreteCategory.congr_hom (NatTrans.congr_app (K.map_id X.val) d) PUnit.unit
  map_comp X Y Z := by
    apply NatTrans.ext
    funext d
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨p, f⟩, ⟨q, g⟩⟩
    exact Prod.ext rfl (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app K X.val Y.val Z.val d f g)

/-- 元の nerve と順序単体の pairing は、同じ基底豊穣関手へ厳密に自然。 -/
lemma d3OrderedCylinderMap_family (K : EnrichedFunctor SSet.{u} C D) (m : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K ⊗ₘ 𝟙 (Δ[m] : SSet.{max u v})) ≫
      EnrichedOrderedCylinder.nerveSimplexFamily m =
    EnrichedOrderedCylinder.nerveSimplexFamily m ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (d3OrderedCylinderMap K m) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  rintro ⟨F, t⟩
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  apply SSet.hom_ext
  intro e
  apply ConcreteCategory.hom_ext
  intro p
  rfl

/-- 前合成した同じ厳密変換の円柱は、元の円柱へ同じ基底関手を前合成したもの。 -/
lemma d3GradedPrecomp_cylinder (K : EnrichedFunctor SSet.{u} C D)
    {F G : EnrichedFunctor SSet.{u} D E}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) :
    StrictEnrichedTransformation.cylinder (K.comp SSet F) (K.comp SSet G)
      (d3GradedPrecomp K η) =
    (d3OrderedCylinderMap K 1).comp SSet (StrictEnrichedTransformation.cylinder F G η) := by
  apply EnrichedFunctor.ext SSet
    (fun X ↦ by rcases X with ⟨j, x⟩; fin_cases j <;> rfl)
  rintro ⟨j, x⟩ ⟨k, y⟩
  fin_cases j <;> fin_cases k
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨p, f⟩
    rfl

/-- 後合成した同じ厳密変換の円柱は、元の円柱へ同じ豊穣関手を後合成したもの。 -/
lemma d3GradedPostcomp_cylinder {F G : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (K : EnrichedFunctor SSet.{u} D E) :
    StrictEnrichedTransformation.cylinder (F.comp SSet K) (G.comp SSet K)
      (d3GradedPostcomp η K) =
    (StrictEnrichedTransformation.cylinder F G η).comp SSet K := by
  apply EnrichedFunctor.ext SSet
    (fun X ↦ by rcases X with ⟨j, x⟩; fin_cases j <;> rfl)
  rintro ⟨j, x⟩ ⟨k, y⟩
  fin_cases j <;> fin_cases k
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨p, f⟩
    solve
    | rfl
    | have hp := p.down.down
      norm_num [Fin.le_def] at hp
    | exact (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.functor_comp_app K _ _ _ d
        ((η.app x).app d PUnit.unit) ((G.map x y).app d f)).symm

/-- 前合成は、指定厳密変換の全区間族を保つ。 -/
lemma d3GradedPrecomp_family (K : EnrichedFunctor SSet.{u} C D)
    {F G : EnrichedFunctor SSet.{u} D E}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G) :
    StrictEnrichedTransformation.family _ _ (d3GradedPrecomp K η) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K ⊗ₘ 𝟙 (Δ[1] : SSet.{max u v})) ≫
        StrictEnrichedTransformation.family F G η := by
  rw [StrictEnrichedTransformation.family, d3GradedPrecomp_cylinder,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp, ← Category.assoc, ← d3OrderedCylinderMap_family]
  rfl

/-- 後合成は、指定厳密変換の全区間族を保つ。 -/
lemma d3GradedPostcomp_family {F G : EnrichedFunctor SSet.{u} C D}
    (η : GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u})) F G)
    (K : EnrichedFunctor SSet.{u} D E) :
    StrictEnrichedTransformation.family _ _ (d3GradedPostcomp η K) =
      StrictEnrichedTransformation.family F G η ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap K := by
  rw [StrictEnrichedTransformation.family, d3GradedPostcomp_cylinder,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap_comp]
  rfl

end SerrePositivity.KST.Spectra

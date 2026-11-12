module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorIsoWhiskerExchange
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyRepresentative
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MapHomotopyCategoryComp
/-!
概要：任意の全関手射の前後合成の交換則と二段後合成則を公開する。
方針：代表辺の積の正方形と、ホモトピー圏に誘導される関手の合成を使う。
規約：可逆性や dg の仮定を加えず、既存の型・証明本文・公開名を保持する。
使われ方：全族比較と導来関手比較に共通する全関手射の計算の入口。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
/-- 等しい通常関手による同じ射の像は型付きで一致する。 -/
lemma functorMapHom_heq_of_functor_eq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) {a b : C} (e : a ⟶ b) : HEq (F.map e) (G.map e) := by
  cases h
  rfl
/-- 元の全関手変換の前後合成は、可逆性なしに同じ指定交換正方形を満たす。 -/
lemma functorHom_whisker_exchange {X Y Z : SSet.{u}} [Quasicategory Y] [Quasicategory Z]
    {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f₀ f₁) (d : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g₀ g₁) :
    (hoFunctor.map ((ihom X).map g₀)).toFunctor.map e ≫
      (hoFunctor.map ((pre f₁).app Z)).toFunctor.map d =
    (hoFunctor.map ((pre f₀).app Z)).toFunctor.map d ≫
      (hoFunctor.map ((ihom X).map g₁)).toFunctor.map e := by
  obtain ⟨ee, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f₁) e
  obtain ⟨dd, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g₁) d
  change Truncated.HomotopyCategory.homMk (ee.map ((truncation 2).map ((ihom X).map g₀))) ≫
      Truncated.HomotopyCategory.homMk (dd.map ((truncation 2).map ((pre f₁).app Z))) =
    Truncated.HomotopyCategory.homMk (dd.map ((truncation 2).map ((pre f₀).app Z))) ≫
      Truncated.HomotopyCategory.homMk (ee.map ((truncation 2).map ((ihom X).map g₁)))
  have h := congrArg
    (fun k ↦ (Truncated.mapHomotopyCategory
      ((truncation 2).map (MonoidalClosed.comp X Y Z))).map k)
    (Truncated.HomotopyCategory.BinaryProduct.square ee dd)
  simp only [Functor.map_comp, Truncated.mapHomotopyCategory_homMk] at h
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.homMk_square_of_edge_eq _ _ _ _
    (ee.map ((truncation 2).map ((ihom X).map g₀)))
    (dd.map ((truncation 2).map ((pre f₁).app Z)))
    (dd.map ((truncation 2).map ((pre f₀).app Z)))
    (ee.map ((truncation 2).map ((ihom X).map g₁))) h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorComposition_post_edge _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorComposition_pre_edge _ _)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorComposition_pre_edge _ _) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorComposition_post_edge _ _)
lemma functorHom_postcomp_postcomp {X Y Z W : SSet.{u}} {f g : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) (p : Y ⟶ Z) (q : Z ⟶ W) :
    (SSet.mapHomotopyCategory ((ihom X).map q)).map
      ((SSet.mapHomotopyCategory ((ihom X).map p)).map e) =
    (SSet.mapHomotopyCategory ((ihom X).map (p ≫ q))).map e := by
  have hn := CategoryTheory.Functor.map_comp (ihom X) p q
  have hh := congrArg (fun k => SSet.mapHomotopyCategory k) hn
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapHomotopyCategory_comp_eq] at hh
  exact (eq_of_heq (functorMapHom_heq_of_functor_eq hh e)).symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories

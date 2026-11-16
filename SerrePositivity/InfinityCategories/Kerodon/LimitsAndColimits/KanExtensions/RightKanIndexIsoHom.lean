module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightHomUniversal
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.PrecompositionHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerHom

/-!
概要：添字写像の指定関手同型による、右 Kan の大域的 Hom 比較写像の移送則。
方針：前合成の既存の自然変換を使い、同じ余単位の類との交換正方形を得る。
Kerodon Proposition 7.3.6.1（Tag 0309）の双対の π₀ の帰結に対する法則。
規約：点ごとの右 Kan 条件への逆向きは主張しない。全関手と指定余単位の類を保持する。
使われ方：反対 Yoneda の二つの指定模型の比較の接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
variable {K C D : SSet.{u}} [Quasicategory C] [Quasicategory D]
  {δ δ' : K ⟶ C} (e : FunctorIso δ δ')

/-- 指定した添字写像の同型は、任意の（可逆とは限らない）全関手変換と交換する。
既存の前合成自然変換の自然性を成分の式で読む。 -/
lemma rightKanIndexIso_whisker_naturality {F G : C ⟶ D} (η : FunctorHom F G) :
    (hoFunctor.map ((pre δ).app D)).toFunctor.map η ≫ (e.postcomp G).hom =
      (e.postcomp F).hom ≫ (hoFunctor.map ((pre δ').app D)).toFunctor.map η := by
  have h := (precompositionNatTrans (functorHomHomotopy e.hom) D).naturality η
  simpa only [precompositionNatTrans_app, functorHomotopyPostcomp_hom,
    functorHomHomotopy_hom, functorIso_postcomp_hom, SSet.hoFunctor, Functor.toCatHom_toFunctor] using h

/-- 同じ指定余単位の類を添字同型に沿って前合成すると、Hom 比較の正方形が可換になる。 -/
lemma rightKanHomMap_indexIso {O : K ⟶ D} {F : C ⟶ D}
    (α : FunctorHom (δ' ≫ F) O) (G : C ⟶ D) (η : FunctorHom G F) :
    rightKanHomMap δ ((e.postcomp F).hom ≫ α) G η =
      (e.postcomp G).hom ≫ rightKanHomMap δ' α G η := by
  unfold rightKanHomMap
  rw [← Category.assoc, rightKanIndexIso_whisker_naturality, Category.assoc]

/-- 添字写像の同型は、同じ全関手と余単位の類に対する大域的 Hom 普遍性を保つ。
Kerodon 7.3.6.1（Tag 0309）の双対の π₀ の帰結のみ。点ごとの右 Kan 条件の代用にはしない。 -/
lemma RightKanHomUniversal.indexIso {O : K ⟶ D} {F : C ⟶ D}
    {α : FunctorHom (δ' ≫ F) O} (hα : RightKanHomUniversal δ' α) :
    RightKanHomUniversal δ ((e.postcomp F).hom ≫ α) := by
  intro G
  let a := e.postcomp G
  have hl : Function.Bijective (fun f : FunctorHom (δ' ≫ G) O => a.hom ≫ f) := by
    constructor
    · intro f g h
      have hh := congrArg (fun f => a.inv ≫ f) h
      simpa only [← Category.assoc, a.inv_hom_id, Category.id_comp] using hh
    · intro f
      refine ⟨a.inv ≫ f, ?_⟩
      change a.hom ≫ (a.inv ≫ f) = f
      rw [← Category.assoc, a.hom_inv_id, Category.id_comp]
  have hh := hl.comp (hα G)
  have he : (fun f : FunctorHom G F => a.hom ≫ rightKanHomMap δ' α G f) =
      rightKanHomMap δ ((e.postcomp F).hom ≫ α) G := by
    funext f
    exact (rightKanHomMap_indexIso e α G f).symm
  change Function.Bijective (fun f : FunctorHom G F => a.hom ≫ rightKanHomMap δ' α G f) at hh
  rw [he] at hh
  exact hh

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

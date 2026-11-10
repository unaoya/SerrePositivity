module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaReflectorLeftKan
public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafNativeDensityKan
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

/-!
概要：余完備な標的への全前層圏からの Yoneda 左 Kan 延長を構成する。
方針：各 Yoneda comma を小さい elements 図式へ戻し、その余極限を取る。
規約：標的の全小余極限を明示し、元の Yoneda と指定単位を保持する。
使われ方：余完備な Ind 模型の前層反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {A : SSet.{u}} [Quasicategory A] {D : SSet.{u + 1}} [Quasicategory D]

/-- 概要：余完備な標的への Yoneda 局所図式は余極限を持つ。
方針：同じ小さい elements 比較で局所図式を制限する。
規約：全前層の任意の頂点を扱う。
使われ方：全前層圏からの左 Kan 延長の存在。 -/
lemma presheafYonedaLeftKanDiagram_hasColimit (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D)
    (v : (PresheafInfinity A) _⦋0⦌) :
    HasColimit (leftKanDiagram (yonedaInfinityMap A) F₀ v) := by
  obtain ⟨F, rfl⟩ := (presheafInfinityObjectEquiv A).surjective v
  change HasColimit (leftKanDiagram (yonedaInfinityMap A) F₀ (functorVertex F))
  apply hasColimit_of_equivalentRestriction (presheafElementsLeftKanComparison F)
    (presheafElementsLeftKanComparison_isQCatEquivalence F)
  rw [leftKanDiagram, ← Category.assoc, presheafElementsLeftKanComparison_projection]
  exact hD _ _

/-- 概要：小余極限を持つ標的への全前層 Yoneda 左 Kan 延長が存在する。
方針：各小 elements 図式の余極限を元の存在定理へ渡す。
規約：全関手と指定単位の coherent な延長を得る。
使われ方：Ind 包含の左随伴候補。 -/
lemma presheaf_exists_yonedaLeftKan (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D) :
    ∃ (L : PresheafInfinity A ⟶ D)
      (β : SSet.Homotopy F₀ (yonedaInfinityMap A ≫ L)),
      IsLeftKanExtension (yonedaInfinityMap A) F₀ L β :=
  F1B.exists_kanLeftExtension_of_local_colimits _ _
    (presheafYonedaLeftKanDiagram_hasColimit hD F₀)

variable {F₀ : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ D}
  {L : PresheafInfinity A ⟶ D}
  (β : SSet.Homotopy F₀ (yonedaInfinityMap A ≫ L))
  (hβ : IsLeftKanExtension (yonedaInfinityMap A) F₀ L β)

include β hβ

/-- 概要：Yoneda 左 Kan 延長の指定単位は可逆。
方針：元の Yoneda の充満忠実性を単位判定へ渡す。
規約：指定単位自体の可逆性。
使われ方：全密度余錐の像の計算。 -/
lemma presheafYonedaLeftKan_unit_isIso :
    IsIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy β)) :=
  leftKanExtension_unit_isIso_of_fullyFaithful _ (yonedaInfinityMap_isFullyFaithful A) β hβ

/-- 概要：Yoneda 左 Kan 延長の元の標準余錐は全て余極限。
方針：同じ可逆単位を指定変換付きの Kan 条件から消去する。
規約：元の候補関手の値を保持する。
使われ方：密度の elements 表示への制限。 -/
lemma presheafYonedaLeftKan_canonicalColimits (v : (PresheafInfinity A) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (yonedaInfinityMap A) L v) :=
  F1B.kanLeftKanExtension_canonicalColimits_of_unit_isIso _ β hβ
    (presheafYonedaLeftKan_unit_isIso β hβ) v

/-- 概要：全前層 Yoneda 左 Kan 延長は元の密度余錐を余極限へ送る。
方針：標準余錐を小さい elements 比較で制限し、全写像を照合する。
規約：元の前層と元の全余錐を保持する。
使われ方：前層反映の制限の回収。 -/
lemma presheafYonedaLeftKan_density_image_isColimit
    (F : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u}) :
    IsColimitCone (mapJoinCocone L (presheafDensityCocone F)) := by
  let c := leftKanCanonicalCocone (yonedaInfinityMap A) L (functorVertex F)
  have hc := (isColimitCone_iff_restrict_equivalentShape (presheafElementsLeftKanComparison F)
    (presheafElementsLeftKanComparison_isQCatEquivalence F) c).mp
      (presheafYonedaLeftKan_canonicalColimits β hβ _)
  apply (F2.isColimitCone_iff_of_cocone_val_eq (c.restrict _)
    (mapJoinCocone L (presheafDensityCocone F)) ?_).mp hc
  change joinMap _ (𝟙 _) ≫ (_ ≫ L) = _
  rw [← Category.assoc]
  exact congrArg (fun g ↦ g ≫ L) (presheafElementsLeftKanComparison_coconeMap F)

end SerrePositivity.InfinityCategories.F2.Presentable

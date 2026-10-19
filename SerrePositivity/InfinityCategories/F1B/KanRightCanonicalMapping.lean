module

public import SerrePositivity.InfinityCategories.F1B.KanRightConstantFamily
public import SerrePositivity.InfinityCategories.F1B.KanRightHomUniversal
public import SerrePositivity.InfinityCategories.F1B.KanPrecompositionMappingPair

/-!
概要：標準右 Kan 関手へ入る元の関手制限の写像空間の同値。
方針：恒等指定変換の局所輸送と Hom 普遍性を定値パラメータ族で適用する。
規約：始点の関手には Kan 条件を要求しない。
使われ方：右 Kan 関手全体からの制限の絶対的な写像空間の普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：恒等指定変換の標準右 Kan 錐の輸送を定値に選ぶ。
方針：標準錐を時刻によらず使う。
規約：元の図式は δ による F の制限。
使われ方：標準局所極限条件を右 Kan の Hom 普遍性へ接続する。 -/
def kanRightReflTransport {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    RightKanConeTransport δ (δ ≫ F) F (functorHomotopyRefl (δ ≫ F)) c where
  family := fst _ (Δ[1] : SSet.{u}) ≫ (rightKanCanonicalCone δ F c).val
  start := by rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]
  diagram := by
    rw [← Category.assoc, whiskerRight_fst, Category.assoc, (rightKanCanonicalCone δ F c).property]
    change fst (rightKanShape δ c) (Δ[1] : SSet.{u}) ≫
      (rightKanProjection δ c ≫ (δ ≫ F)) =
        (rightKanProjection δ c ▷ (Δ[1] : SSet.{u})) ≫
          (fst K (Δ[1] : SSet.{u}) ≫ (δ ≫ F))
    simp only [reassoc_of% (whiskerRight_fst (rightKanProjection δ c) (Δ[1] : SSet.{u}))]
  fixedVertex := by rw [← Category.assoc, whiskerRight_fst, Category.assoc]

/-- 概要：標準局所錐の極限性は恒等指定変換に対する右 Kan 条件を与える。
方針：恒等変換の定値な局所輸送を選び、終端を標準錐と同定する。
規約：δ に fibration 性や単射性を要求しない。
使われ方：標準条件から保存済みの右 Kan の Hom 普遍性へ進む。 -/
lemma kanRightKanExtension_refl_of_canonicalLimits {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, IsLimitCone (rightKanCanonicalCone δ F c)) :
    IsRightKanExtension δ (δ ≫ F) F (functorHomotopyRefl (δ ≫ F)) := by
  intro c
  refine ⟨kanRightReflTransport δ F c, ?_⟩
  have he : (kanRightReflTransport δ F c).cone = rightKanCanonicalCone δ F c := by
    apply Subtype.ext
    change SSet.ι₁ ≫ (fst _ (Δ[1] : SSet.{u}) ≫ _) = _
    rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
  rw [he]
  exact hF c

/-- 概要：標準右 Kan 関手へ入る h Fun の射の制限は全単射。
方針：恒等指定変換の右 Hom 普遍性から後置された恒等射を消去する。
規約：始点 G の局所普遍性は不要。
使われ方：全パラメータの右 Kan の写像空間比較。 -/
lemma kanRightCanonicalHomMap_bijective {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, IsLimitCone (rightKanCanonicalCone δ F c)) (G : C ⟶ D) :
    Function.Bijective
      ((hoFunctor.map ((pre δ).app D)).toFunctor.map : FunctorHom G F → _) := by
  have h := kanRightKanExtension_homUniversal δ (functorHomotopyRefl (δ ≫ F))
    (kanRightKanExtension_refl_of_canonicalLimits δ F hF) G
  rw [functorHomotopyRefl_hom] at h
  change Function.Bijective (fun α : FunctorHom G F ↦
    (hoFunctor.map ((pre δ).app D)).toFunctor.map α ≫ 𝟙 _) at h
  simpa only [Category.comp_id] using h

/-- 概要：標準右 Kan 関手へ入る元の制限の右 pinched 写像はホモトピー同値。
方針：局所極限を定値族へ移し、転置後の Hom 全単射を指定比較の判定へ渡す。
規約：δ の単射性と G の局所普遍性は不要。
使われ方：元の右 Kan 関手の制限の絶対的な写像空間の普遍性。 -/
lemma kanRightCanonical_pinchedHomMap_equivalence {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F : C ⟶ D)
    (hF : ∀ c : C _⦋0⦌, IsLimitCone (rightKanCanonicalCone δ F c)) (G : C ⟶ D) :
    IsSimplicialHomotopyEquivalence
      (pinchedHomMap ((pre δ).app D) (functorVertex G) (functorVertex F)) :=
  kanPrecomposition_pinchedHomMap_equivalence_of_constantFamily δ G F
    (fun A ↦ kanRightCanonicalHomMap_bijective δ (F ≫ constantFunctorMap A D)
      (kanRightCanonicalLimits_constantFamily δ F hF) (G ≫ constantFunctorMap A D))

end SerrePositivity.InfinityCategories.F1B

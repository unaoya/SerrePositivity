module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PostcompositionHomotopy
public import SerrePositivity.InfinityCategories.HomotopyLimits.ArbitraryParameterAdjunct

/-!
概要：任意の添字 K について、元の同じ標準単位から後合成の ∞ 随伴を構成する。
方針：同じ標準単位の式と、直積パラメータ上の Hom 全単射を照合する。
規約：添字の quasicategory 性を仮定しない。使われ方：一般 coherent 極限の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section

/-- 同じ標準単位の Hom 比較は、元の二胞体の uncurry と可換。 -/
lemma parameterUnitHomMap_uncurry {K A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (H : SSet.Homotopy (𝟙 X) (F ≫ G))
    (U : A ⟶ (ihom K).obj X) (V : A ⟶ (ihom K).obj Y)
    (α : FunctorHom (U ≫ (ihom K).map F) V) :
    functorHomUncurry (K := K) (A := A) (X := X)
      (U := U) (V := V ≫ (ihom K).map G) (parameterUnitHomMap
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (postcompositionUnitHomotopy H K))) U V α) =
    parameterUnitHomMap (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy H)) (uncurry U) (uncurry V)
      (functorHomUncurry (K := K) (A := A) (X := Y)
        (U := U ≫ (ihom K).map F) (V := V) α) := by
  have hm := functorHomUncurry_comp (K := K) (A := A) (X := X)
    (U := U) (V := U ≫ (ihom K).map F ≫ (ihom K).map G)
    (W := V ≫ (ihom K).map G)
    ((hoFunctor.map ((pre U).app ((ihom K).obj X))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (postcompositionUnitHomotopy H K))))
    ((hoFunctor.map ((ihom A).map ((ihom K).map G))).toFunctor.map α)
  exact hm.trans (congrArg₂ (· ≫ ·)
    (functorHomUncurry_unit_precomp (K := K) (A := A) H U)
    (functorHomUncurry_postcomp (K := K) (A := A) α G))

/-- 任意の関手パラメータ上の後合成の標準単位 Hom 比較は全単射。 -/
lemma parameterUnitHomMap_postcomposition_bijective {K A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (𝟙 X) (F ≫ G))
    (hH : UnitMappingSpaceCondition
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)))
    (U : A ⟶ (ihom K).obj X) (V : A ⟶ (ihom K).obj Y) :
    Function.Bijective (parameterUnitHomMap
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (postcompositionUnitHomotopy H K))) U V) := by
  have hs := functorHomUncurry_bijective (K := K) (A := A) (X := Y) (U ≫ (ihom K).map F) V
  have ht := functorHomUncurry_bijective (K := K) (A := A) (X := X) U (V ≫ (ihom K).map G)
  have hb := parameterUnitHomMap_bijective
    (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) hH
    (uncurry U) (uncurry V)
  constructor
  · intro α β he
    apply hs.injective
    apply hb.injective
    rw [← parameterUnitHomMap_uncurry, ← parameterUnitHomMap_uncurry, he]
  · intro β
    obtain ⟨αu, hαu⟩ := hb.surjective (functorHomUncurry (K := K) (A := A) (X := X)
      (U := U) (V := V ≫ (ihom K).map G) β)
    obtain ⟨α', rfl⟩ := hs.surjective αu
    refine ⟨α', ht.injective ?_⟩
    rw [parameterUnitHomMap_uncurry]
    exact hαu

/-- quasicategory パラメータ上の標準単位 Hom 比較も、同じ式で全単射。 -/
lemma qcatUnitHomMap_postcomposition_bijective {K A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (H : SSet.Homotopy (𝟙 X) (F ≫ G))
    (hH : UnitMappingSpaceCondition
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)))
    (U : A ⟶ (ihom K).obj X) (V : A ⟶ (ihom K).obj Y) :
    Function.Bijective (qcatUnitHomMap
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (postcompositionUnitHomotopy H K))) U V) := by
  have hb := parameterUnitHomMap_postcomposition_bijective H hH U V
  have he : parameterUnitHomMap
      (SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (postcompositionUnitHomotopy H K))) U V =
    qcatUnitHomMap (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (postcompositionUnitHomotopy H K))) U V := by
    funext α
    exact parameterUnitHomMap_eq _ U V α
  rw [← he]
  exact hb

/-- 任意の添字で、元の標準単位のホモトピーから後合成の ∞ 随伴を構成する。 -/
def postcompositionAdjunctionOfUnitHomotopy {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (𝟙 X) (F ≫ G))
    (hH : UnitMappingSpaceCondition
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)))
    (K : SSet.{u}) : QCatAdjunction ((ihom K).map F) ((ihom K).map G) :=
  qcatAdjunctionOfUnitHomBijective
    (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (postcompositionUnitHomotopy H K)))
    (fun U V ↦ qcatUnitHomMap_postcomposition_bijective H hH U V)

/-- 構成した後合成の随伴の単位は、元の指定単位から作ったものと一致する。 -/
lemma postcompositionAdjunctionOfUnitHomotopy_unitHom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (𝟙 X) (F ≫ G))
    (hH : UnitMappingSpaceCondition
      (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)))
    (K : SSet.{u}) : (postcompositionAdjunctionOfUnitHomotopy H hH K).unitHom =
      SSet.Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (postcompositionUnitHomotopy H K)) := by
  exact qcatAdjunctionOfUnitHomBijective_unitHom _
    (fun U V ↦ qcatUnitHomMap_postcomposition_bijective H hH U V)

/-- 元の ∞ 随伴を、任意の添字の関手圏の後合成の ∞ 随伴に移す。 -/
def postcompositionAdjunction {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : QCatAdjunction F G) (K : SSet.{u}) :
    QCatAdjunction ((ihom K).map F) ((ihom K).map G) := by
  have hH : UnitMappingSpaceCondition (SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomHomotopy a.unitHom))) := by
    rw [functorHomHomotopy_hom]
    exact a.unitMappingSpaceCondition
  exact postcompositionAdjunctionOfUnitHomotopy (functorHomHomotopy a.unitHom) hH K

end
end SerrePositivity.InfinityCategories.HomotopyLimits

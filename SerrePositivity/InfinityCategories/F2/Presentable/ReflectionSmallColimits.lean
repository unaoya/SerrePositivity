module

public import SerrePositivity.InfinityCategories.F2.Presentable.LeftAdjointAllColimitPreservation
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaReflectorAdjunction
public import SerrePositivity.InfinityCategories.F1B.Localization.ReflectiveIdempotence

/-!
概要：前層の反映模型で元の任意小図式の余極限を構成する。
方針：周囲の native な余極限を反映し、可逆な余単位で元の図式へ戻す。
規約：一般 Bousfield 局所化の存在は使用しない。
使われ方：presentable 圏の反映表示と小余極限の具体的構成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits

/-- 概要：余完備な圏の反映された全部分圏は全小余極限を持つ。
方針：元の反映の可逆な余単位を一般構成へ渡す。
規約：頂点条件に同型不変性は要求しない。
使われ方：前層反映による余完備性。 -/
lemma reflectiveSubcategory_hasSmallColimits {X : SSet.{u + 1}} [Quasicategory X]
    {P : X _⦋0⦌ → Prop} (r : ReflectiveSubcategory X P) (hX : HasSmallColimits X) :
    HasSmallColimits (fullSubcomplexOnVertices X P : SSet.{u + 1}) :=
  hasSmallColimits_of_reflection r.adjunction r.counitIso hX

/-- 概要：P_Σ の指定反映は任意の小形状の全余極限を保存する。
方針：構成済みの専用随伴を形状無制限の保存定理へ渡す。
規約：同じ左 Kan 候補を保持する。
使われ方：前層の余極限の反映による元の余極限の計算。 -/
lemma sigmaReflector_preservesSmallColimits {A : SSet.{u}} [Quasicategory A]
    {L : PresheafInfinity A ⟶ SigmaPresheafInfinity A}
    (β : SSet.Homotopy (sigmaYonedaInfinityMap A) (yonedaInfinityMap A ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap A) (sigmaYonedaInfinityMap A) L β) :
    PreservesSmallColimits L :=
  adjunction_preservesSmallColimits (sigmaReflectorAdjunction β hβ)

/-- 概要：P_Σ の任意の小図式の余極限を前層余極限の反映で構成する。
方針：同じ専用反映の余単位同型で元の図式を回収する。
規約：有限余積条件は構成済みの反映に含まれ、ここでは候補と Kan 条件だけを使う。
使われ方：任意小形状の native な余極限の存在。 -/
lemma sigma_hasColimit_of_reflector {A : SSet.{u}} [Quasicategory A]
    {L : PresheafInfinity A ⟶ SigmaPresheafInfinity A}
    (β : SSet.Homotopy (sigmaYonedaInfinityMap A) (yonedaInfinityMap A ≫ L))
    (hβ : IsLeftKanExtension (yonedaInfinityMap A) (sigmaYonedaInfinityMap A) L β)
    {K : SSet.{u}} (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ SigmaPresheafInfinity A) :
    HasColimit D := by
  have : IsIso (sigmaReflectorAdjunction β hβ).counitHom := by
    apply (sigmaReflectorAdjunction β hβ).counitHom_isIso_of_postcompFullyFaithful
    exact fullSubcomplexFunctorInclusionHoFullyFaithful _ _ _
  exact hasColimit_of_reflection (sigmaReflectorAdjunction β hβ)
    (asIso (sigmaReflectorAdjunction β hβ).counitHom) D
    (presheaf_hasSmallColimits A K (D ≫ sigmaPresheafInfinityInclusion A))

end SerrePositivity.InfinityCategories.F2.Presentable

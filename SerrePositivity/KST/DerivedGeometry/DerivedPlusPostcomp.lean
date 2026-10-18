module

public import SerrePositivity.KST.DerivedGeometry.ExactDerivedPlusFactors
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
概要：bounded below 導来関手の随伴に必要な後合成での導来性。
方針：完全左導来の比較同型と、injective 模型での右導来の比較同型の判定を使う。
規約：後合成関手の完全性を要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の bounded below 導来随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C D E : Type*} [Category* C] [Category* D] [Category* E] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/--
概要：完全関手の bounded below 左導来は任意の後合成の後も左導来関手。
方針：局所化との比較同型を後合成し、反転する関手の左導来の普遍性を使う。
規約：後合成の保存性を仮定しない。
使われ方：TT §3、Toën §3.2 の導来随伴の存在。
-/
lemma exactDerivedPlus_postcomp_isLeftDerivedFunctor (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (P : DerivedCategory.Plus D ⥤ E) :
    (exactDerivedFunctorPlus F ⋙ P).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight (exactDerivedFunctorPlusFactors F).hom P)
      (CochainComplex.Plus.quasiIso C) :=
  Functor.isLeftDerivedFunctor_of_inverts (CochainComplex.Plus.quasiIso C) _
    (asIso ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (exactDerivedFunctorPlusFactors F).hom P))

/--
概要：bounded below 右導来関手は任意の後合成の後も右導来関手。
方針：injective 模型で比較が同型であることを後合成へ移し、導来性の判定を使う。
規約：十分な injective は元の圏に要求し、分解の存在をフィールドにしない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の導来随伴の存在。
-/
lemma rightDerivedPlus_postcomp_isRightDerivedFunctor [EnoughInjectives C]
    (G : C ⥤ D) [G.Additive] (P : DerivedCategory.Plus D ⥤ E) :
    (G.rightDerivedFunctorPlus ⋙ P).IsRightDerivedFunctor
      (Functor.whiskerRight G.rightDerivedFunctorPlusUnit P ≫ (Functor.associator _ _ _).hom)
      (CochainComplex.Plus.quasiIso C) := by
  have h : (CochainComplex.Plus.localizerMorphism C).Derives
      ((G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ⋙ P) := by
    intro K L f hf
    have : IsIso ((G.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).map
        ((CochainComplex.Plus.localizerMorphism C).functor.map f)) :=
      (CochainComplex.Plus.localizerMorphism_derives_mapCochainComplexPlus G) f hf
    exact Functor.map_isIso P _
  apply h.isRightDerivedFunctor_of_isIso
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app]
  change IsIso (P.map (G.rightDerivedFunctorPlusUnit.app
    ((InjectiveObject.ι C).mapCochainComplexPlus.obj K)) ≫ 𝟙 _)
  infer_instance

end SerrePositivity.KST.DerivedGeometry

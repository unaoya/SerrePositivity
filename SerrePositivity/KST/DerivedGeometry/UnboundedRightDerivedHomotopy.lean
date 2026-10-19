module

public import SerrePositivity.KST.DerivedGeometry.UnboundedKInjectiveDerivability

/-!
概要：非有界ホモトピー圏の任意の関手の右導来関手とその後合成の普遍性。
方針：局所化の K-injective 右随伴と合成し、右導来構造で普遍性を証明する。
規約：右導来関手の存在を仮定せず実際に構成する。
使われ方：TT §3・§8、Toën §3.2 の非有界右導来大域切断と導来随伴。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w v u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable (C : Type u) [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  [HasDerivedCategory.{v} C]

/--
概要：既に K-injective なホモトピー対象で分解の単位は同型。
方針：導来比較の完全忠実性で、局所化後に同型な単位を反映する。
規約：分解の射の実際の同型性。
使われ方：TT §3、Toën §3.2 の右導来性の判定。
-/
lemma kInjectiveReplacementUnit_isIso (X : (kInjectiveHomotopyObjects C).FullSubcategory) :
    IsIso ((kInjectiveReplacementUnit C).app X.obj) := by
  let f : X ⟶ (kInjectiveReplacementFunctor C).obj X.obj :=
    ObjectProperty.homMk ((kInjectiveReplacementUnit C).app X.obj)
  have : IsIso ((kInjectiveDerivedFunctor C).map f) :=
    kInjectiveLocalizationAdjunction_map_unit_isIso C X.obj
  have : IsIso f := isIso_of_reflects_iso f (kInjectiveDerivedFunctor C)
  exact CategoryTheory.Functor.map_isIso (kInjectiveHomotopyObjects C).ι f

variable {E : Type*} [Category* E]

/--
概要：非有界導来圏上の右導来関手。
方針：局所化の構成済み右随伴と元の関手を合成する。
規約：標的圏は任意。
使われ方：TT §3、Toën §3.2 の非有界右導来関手。
-/
def unboundedRightDerivedHomotopy (F : HomotopyCategory C (.up ℤ) ⥤ E) : DerivedCategory C ⥤ E :=
  kInjectiveLocalizationRightAdjoint C ⋙ F

/--
概要：元の関手から構成した非有界右導来関手への単位。
方針：局所化の随伴の単位を後合成する。
規約：自然変換の結合子を明示する。
使われ方：TT §3、Toën §3.2 の右導来性の普遍性。
-/
def unboundedRightDerivedHomotopyUnit (F : HomotopyCategory C (.up ℤ) ⥤ E) :
    F ⟶ DerivedCategory.Qh ⋙ unboundedRightDerivedHomotopy C F :=
  (CategoryTheory.Functor.leftUnitor F).inv ≫
    CategoryTheory.Functor.whiskerRight (kInjectiveLocalizationAdjunction C).unit F ≫
    (CategoryTheory.Functor.associator _ _ _).hom

/--
概要：構成した非有界関手は実際に右導来関手。
方針：K-injective 模型で単位が同型であることと導来構造の判定を使う。
規約：単位の同型性を仮定のフィールドにしない。
使われ方：TT §3・§8、Toën §3.2 の非有界右導来大域切断。
-/
instance unboundedRightDerivedHomotopy_isRightDerivedFunctor (F : HomotopyCategory C (.up ℤ) ⥤ E) :
    (unboundedRightDerivedHomotopy C F).IsRightDerivedFunctor
      (unboundedRightDerivedHomotopyUnit C F) (HomotopyCategory.quasiIso C (.up ℤ)) := by
  apply (kInjectiveLocalizerMorphism_derives C F).isRightDerivedFunctor_of_isIso
  intro X
  change IsIso ((unboundedRightDerivedHomotopyUnit C F).app X.obj)
  have : IsIso ((kInjectiveLocalizationAdjunction C).unit.app X.obj) :=
    kInjectiveReplacementUnit_isIso C X
  dsimp only [unboundedRightDerivedHomotopyUnit, NatTrans.comp_app,
    CategoryTheory.Functor.leftUnitor_inv_app, CategoryTheory.Functor.whiskerRight_app,
    CategoryTheory.Functor.associator_hom_app]
  infer_instance

/--
概要：構成した非有界右導来関手は任意の後合成の後も右導来関手。
方針：同じ K-injective 模型で単位の同型性が後合成で保たれることを使う。
規約：後合成の極限・余極限保存性を仮定しない。
使われ方：TT §3、Toën §3.2 の非有界導来随伴の存在。
-/
lemma unboundedRightDerivedHomotopy_postcomp {E' : Type*} [Category* E']
    (F : HomotopyCategory C (.up ℤ) ⥤ E) (P : E ⥤ E') :
    (unboundedRightDerivedHomotopy C F ⋙ P).IsRightDerivedFunctor
      (CategoryTheory.Functor.whiskerRight (unboundedRightDerivedHomotopyUnit C F) P ≫
        (CategoryTheory.Functor.associator _ _ _).hom)
      (HomotopyCategory.quasiIso C (.up ℤ)) := by
  apply (kInjectiveLocalizerMorphism_derives C (F ⋙ P)).isRightDerivedFunctor_of_isIso
  intro X
  have : IsIso ((unboundedRightDerivedHomotopyUnit C F).app X.obj) := by
    dsimp only [unboundedRightDerivedHomotopyUnit, NatTrans.comp_app,
      CategoryTheory.Functor.leftUnitor_inv_app, CategoryTheory.Functor.whiskerRight_app,
      CategoryTheory.Functor.associator_hom_app]
    have : IsIso ((kInjectiveLocalizationAdjunction C).unit.app X.obj) :=
      kInjectiveReplacementUnit_isIso C X
    infer_instance
  change IsIso (P.map ((unboundedRightDerivedHomotopyUnit C F).app X.obj) ≫ 𝟙 _)
  infer_instance

end SerrePositivity.KST.DerivedGeometry

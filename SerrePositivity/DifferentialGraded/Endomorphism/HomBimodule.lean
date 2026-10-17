module
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Bimodule.Identity
public import SerrePositivity.DifferentialGraded.Bimodule.OfActions
public import SerrePositivity.DifferentialGraded.Module.Restriction
public import SerrePositivity.DifferentialGraded.Perfect.SmallEnhancement

/-! # 指定対象からのHomを値とするendomorphism bimodule -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D] (E : D)

/-- Hom(E,X)の右End(E)作用は、代表加群の指定対象への制限である。 -/
def endomorphismHomRight (X : D) : RightModule A (EndomorphismObject E) :=
  restrictModule A _ D (endomorphismInclusion A E).op (representable A X)

/-- Yonedaの全次数自然族を一対象上に制限する。 -/
def endomorphismHomParam (X Y : D) :
    ModuleParamTrans A (EndomorphismObject E) (X ⟶[Complex A] Y)
      (endomorphismHomRight A D E X) (endomorphismHomRight A D E Y) where
  app _ := ((Bimodule.diagonal A D).paramTrans X Y).app (op E)
  naturality x y := by
    change (β_ (X ⟶[Complex A] Y) (op E ⟶[Complex A] op E)).hom ≫
      ((𝟙 _ ≫ (representable A X).map (op E) (op E)) ⊗ₘ
        ((Bimodule.diagonal A D).paramTrans X Y).app (op E)) ≫ enrichedComposition _ _ _ =
      (((Bimodule.diagonal A D).paramTrans X Y).app (op E) ⊗ₘ
        (𝟙 _ ≫ (representable A Y).map (op E) (op E))) ≫ enrichedComposition _ _ _
    simp only [Category.id_comp]
    exact ((Bimodule.diagonal A D).paramTrans X Y).naturality (op E) (op E)

/-- 右End(E)・左Dのbimodule。全次数Hom endに値を持つ。 -/
def endomorphismHomBimodule : Bimodule A (EndomorphismObject E) D :=
  Bimodule.ofParamTrans A _ D (endomorphismHomRight A D E)
    (endomorphismHomParam A D E)
    (fun X _ => (Bimodule.diagonal A D).paramTrans_unit X (op E))
    (fun X Y Z _ => (Bimodule.diagonal A D).paramTrans_comp X Y Z (op E))

/-- bimoduleの値は指定対象からの全Hom複体。 -/
lemma endomorphismHomBimodule_value (b : EndomorphismObject E) (X : D) :
    (endomorphismHomBimodule A D E).value b X = homObject A D E X := rfl

/-- 既存Yonedaとの比較：各右加群はYoneda像の制限そのもの。 -/
lemma endomorphismHomBimodule_rightAt (X : D) :
    (endomorphismHomBimodule A D E).rightAt X =
      restrictModule A _ D (endomorphismInclusion A E).op ((dgYoneda A D).obj X) := rfl

/-- 左D作用の成分は既存dg YonedaのHom写像のE成分。 -/
lemma endomorphismHomBimodule_map_π (X Y : D) (b : EndomorphismObject E) :
    (endomorphismHomBimodule A D E).map X Y ≫
      moduleHomπ A _ (endomorphismHomRight A D E X) (endomorphismHomRight A D E Y) b =
    yonedaHom A D X Y ≫ moduleHomπ A D (representable A X) (representable A Y) E :=
  Bimodule.ofParamTrans_map_π A _ D _ _ _ _ X Y b

omit [Small.{u} D] in
/-- E自身の像はEnd(E)の正則右加群。全次数の作用も一致する。 -/
lemma endomorphismHomRight_self :
    endomorphismHomRight A D E E = representable A (EndomorphismObject.point (E := E)) := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

/-- U13の小さいenhancement内の指定対象に対するEnd表示bimodule。 -/
abbrev perfectEndomorphismHomBimodule (S : Set D) (E : SmallPerfectDGModuleOver A D S) :=
  endomorphismHomBimodule A (SmallPerfectDGModuleOver A D S) E

end SerrePositivity.DifferentialGraded

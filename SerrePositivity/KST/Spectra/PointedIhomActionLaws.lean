module

public import SerrePositivity.KST.Spectra.PointedIhomActionComposition

/-!
概要：点つき内部 Hom の全パラメータ作用の恒等・合成保存。
方針：二回の評価を元の閉構造の豊穣単位・結合律へ戻す。
規約：通常射だけの関手法則に弱めない。
使われ方：補助 loop の全 Hom 作用と相対右射影の豊穣合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 概要：閉構造の表現 Hom の全パラメータ作用は合成を保つ。
方針：抽象閉圏で二回の評価と結合律を照合する。
規約：具体的な選択極限を展開しない。
使われ方：点つき内部 Hom の合成保存への特殊化。 -/
private lemma closedAction_comp {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] (A X Y Z : C) :
    comp X Y Z ≫ curry (comp A X Z) =
      (curry (comp A X Y) ⊗ₘ curry (comp A Y Z)) ≫
        comp ((ihom A).obj X) ((ihom A).obj Y) ((ihom A).obj Z) := by
  apply uncurry_injective
  simp only [uncurry_natural_left, uncurry_curry]
  rw [comp_eq ((ihom A).obj X) ((ihom A).obj Y) ((ihom A).obj Z),
    uncurry_curry, compTranspose_eq]
  conv_rhs => rw [← id_tensorHom, associator_inv_naturality_assoc]
  rw [id_tensorHom, tensorHom_comp_whiskerRight_assoc, ← uncurry_eq, uncurry_curry]
  rw [tensorHom_def, Category.assoc]
  simp only [CategoryTheory.Functor.id_obj]
  rw [← uncurry_eq, uncurry_curry]
  exact (MonoidalClosed.assoc A X Y Z).symm

/-- 概要：内部 Hom の全パラメータ作用は元の豊穣合成を保つ。
方針：抽象閉圏で証明した二回の評価の結合律を特殊化する。
規約：全 smash パラメータ上の厳密等式。
使われ方：相対 BF 右射影の全 Hom 合成の保持。 -/
lemma ihomAction_comp (A X Y Z : PointedSimplicialSet.{u}) :
    comp X Y Z ≫ ihomAction A X Z =
      (ihomAction A X Y ⊗ₘ ihomAction A Y Z) ≫
        comp (PointedObject.basedHom A X) (PointedObject.basedHom A Y)
          (PointedObject.basedHom A Z) := by
  simp only [ihomAction_eq_curry_comp]
  exact closedAction_comp A X Y Z

/-- 概要：閉構造の表現 Hom の全パラメータ作用は恒等射を保つ。
方針：抽象閉圏で評価の右単位律を使う。
規約：具体的な選択極限を展開しない。
使われ方：点つき内部 Hom の単位保存への特殊化。 -/
private lemma closedAction_id {C : Type*} [Category C] [MonoidalCategory C]
    [MonoidalClosed C] (A X : C) :
    MonoidalClosed.id X ≫ curry (comp A X X) = MonoidalClosed.id ((ihom A).obj X) := by
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_curry,
    MonoidalClosed.id_eq ((ihom A).obj X), uncurry_curry]
  apply (cancel_epi (ρ_ ((ihom A).obj X)).inv).mp
  rw [MonoidalClosed.comp_id, Iso.inv_hom_id]

/-- 概要：内部 Hom の全パラメータ作用は元の豊穣恒等射を保つ。
方針：抽象閉圏で証明した評価の右単位律を特殊化する。
規約：元の豊穣単位の厳密等式。
使われ方：補助 loop の全 Hom 作用の単位法則。 -/
lemma ihomAction_id (A X : PointedSimplicialSet.{u}) :
    MonoidalClosed.id X ≫ ihomAction A X X =
      MonoidalClosed.id (PointedObject.basedHom A X) := by
  rw [ihomAction_eq_curry_comp]
  exact closedAction_id A X

local instance pointedIhomActionLawsLocal1 : EnrichedCategory PointedSimplicialSet.{u} PointedSimplicialSet.{u} :=
  enrichedCategorySelf PointedSimplicialSet.{u}

/-- 概要：元の内部 Hom の作用を全パラメータの豊穣関手へ束ねる。
方針：元の評価から定義された作用と実単位・合成保存を使う。
規約：対象の Kan 性や通常射だけの自然性を入力にしない。
使われ方：補助 loop 列の全 Hom 作用の恒等・合成保存。 -/
def ihomEnrichedFunctor (A : PointedSimplicialSet.{u}) :
    EnrichedFunctor PointedSimplicialSet.{u} PointedSimplicialSet.{u} PointedSimplicialSet.{u} where
  obj X := PointedObject.basedHom A X
  map X Y := ihomAction A X Y
  map_id X := ihomAction_id A X
  map_comp X Y Z := ihomAction_comp A X Y Z

local instance pointedIhomActionLawsLocal2 : SimplicialCategory PointedSimplicialSet.{u} :=
  PointedEnrichment.simplicialCategory

/-- 概要：同じ内部 Hom の作用は全単体的 Hom を保つ実豊穣関手。
方針：点つき作用の実単位・合成保存を smash 忘却に沿って移す。
規約：Kan 性や新たな関手法則を入力しない。
使われ方：補助 loop 作用の全 Hom 合成を段ごとに照合する。 -/
def ihomSimplicialFunctor (A : PointedSimplicialSet.{u}) :
    EnrichedFunctor SSet.{u} PointedSimplicialSet.{u} PointedSimplicialSet.{u} where
  obj X := PointedObject.basedHom A X
  map X Y := (ihomAction A X Y).right
  map_id X := by
    change (PointedSimplicialSet.forgetUnit ≫ (MonoidalClosed.id X).right) ≫
      (ihomAction A X X).right = _
    rw [Category.assoc, ← Under.comp_right, ihomAction_id]
    rfl
  map_comp X Y Z := by
    change (PointedSimplicialSet.productToSmash _ _ ≫ (comp X Y Z).right) ≫
      (ihomAction A X Z).right = _
    rw [Category.assoc, ← Under.comp_right, ihomAction_comp, Under.comp_right,
      ← Category.assoc, ← PointedSimplicialSet.productToSmash_naturality, Category.assoc]
    rfl

end SerrePositivity.KST.Spectra.PointedMapping

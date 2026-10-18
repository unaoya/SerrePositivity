module

public import SerrePositivity.InfinityCategories.F1B.QCatUnitHomCriterion

/-!
概要：指定単位による Hom 比較を内部 Hom の前後合成で表示する。
方針：QCat の構造二胞体を厳密性で相殺し、左・右 whisker の比較を使う。
規約：η は任意の単位候補で、随伴の存在を仮定しない。
使われ方：Kerodon Cor 6.2.6.5 の標準的な単位による比較の認識。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Bicategory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
local instance unitFormulaHomCategory (A B : SSet.QCat.{u}) : Category.{u} (A ⟶ B) :=
  SSet.QCat.bicategory.homCategory A B

/-- 概要：単位の Hom 比較は U による前合成と G による後合成の合成。
方針：双圏の単位の公式で現れる単位子・結合子を消し、whisker を表示する。
規約：端点 U,V は非定値でよい。
使われ方：単位の各点の公式と全パラメータ版を照合する。 -/
lemma qcatUnitHomMap_formula {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (U : A ⟶ X) (V : A ⟶ Y) (α : FunctorHom (U ≫ F) V) :
    qcatUnitHomMap η U V α =
      (hoFunctor.map ((pre U).app X)).toFunctor.map η ≫
        (hoFunctor.map ((ihom A).map G)).toFunctor.map α := by
  let η' := (qcatCellEquiv (𝟙 X) (F ≫ G)).symm η
  let α' := (qcatCellEquiv (U ≫ F) V).symm α
  have hl := qcatCell_whiskerLeft U η'
  have hr := qcatCell_whiskerRight α' G
  unfold qcatUnitHomMap bicategoryUnitHomMap
  simp only [Bicategory.Strict.rightUnitor_eqToIso, Bicategory.Strict.associator_eqToIso,
    eqToIso.inv, eqToHom_refl, Category.id_comp]
  change qcatCellEquiv _ _ (qcatMap U ◁ η') ≫
    qcatCellEquiv _ _ (α' ▷ qcatMap G) = _
  exact congrArg₂ (· ≫ ·) hl hr

/-- 概要：単位による比較は終域側の合成に自然。
方針：内部 Hom の後合成の関手性と結合則を使う。
規約：単位の普遍性は不要。
使われ方：自然な写像空間比較の終域自然性の認識。 -/
lemma qcatUnitHomMap_naturality_right {A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (U : A ⟶ X) (V V' : A ⟶ Y) (α : FunctorHom (U ≫ F) V) (β : FunctorHom V V') :
    qcatUnitHomMap η U V' (α ≫ β) = qcatUnitHomMap η U V α ≫
      (hoFunctor.map ((ihom A).map G)).toFunctor.map β := by
  simp only [qcatUnitHomMap_formula, Functor.map_comp, Category.assoc]

/-- 概要：単位による比較はパラメータ前合成に自然。
方針：双圏の単位写像の左 whisker の自然性を内部 Hom の pre へ移す。
規約：A,B は quasicategory。単位が随伴の単位であるとは仮定しない。
使われ方：単位による全パラメータ比較の整合。 -/
lemma qcatUnitHomMap_precomp {A B X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (η : FunctorHom (𝟙 X) (F ≫ G))
    (i : A ⟶ B) (U : B ⟶ X) (V : B ⟶ Y) (α : FunctorHom (U ≫ F) V) :
    qcatUnitHomMap η (i ≫ U) (i ≫ V) ((hoFunctor.map ((pre i).app Y)).toFunctor.map α) =
      (hoFunctor.map ((pre i).app X)).toFunctor.map (qcatUnitHomMap η U V α) := by
  obtain ⟨α', rfl⟩ := (qcatCellEquiv (U ≫ F) V).surjective α
  rw [← qcatCell_whiskerLeft i α']
  change qcatCellEquiv _ _
    (bicategoryUnitHomMap ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η)
      (qcatMap (i ≫ U)) (qcatMap (i ≫ V)) (qcatMap i ◁ α')) =
    (hoFunctor.map ((pre i).app X)).toFunctor.map
      (qcatCellEquiv _ _
        (bicategoryUnitHomMap ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η)
          (qcatMap U) (qcatMap V) α'))
  rw [← qcatCell_whiskerLeft]
  have h := bicategoryUnitHomMap_precomp ((qcatCellEquiv (𝟙 X) (F ≫ G)).symm η)
    (qcatMap i) α'
  simp only [Bicategory.Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    eqToHom_refl, Category.id_comp, Category.comp_id] at h
  exact congrArg (qcatCellEquiv (i ≫ U) ((i ≫ V) ≫ G)) h

end SerrePositivity.InfinityCategories

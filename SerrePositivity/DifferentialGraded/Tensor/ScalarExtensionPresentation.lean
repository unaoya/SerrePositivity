module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionActions
public import SerrePositivity.DifferentialGraded.Tensor.Balanced

/-! # balanced tensor の直和表示の係数変更 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.ScalarExtension
open CategoryTheory MonoidalCategory HomologicalComplex Opposite Limits
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (M : RightModule A D) (N : LeftModule A D)

/-- 三つの tensor 因子の係数変更を左括弧のまま行う。 -/
abbrev tripleIso (K L T : Complex A) := cochainTensorTripleBaseChangeIso φ K L T

lemma tripleIso_hom (K L T : Complex A) :
    (tripleIso φ K L T).hom = (tensorIso φ (K ⊗ L) T).hom ≫
      (tensorIso φ K L).hom ▷ (extension φ).obj T := rfl

/-- 元と同じ対象添字を使う生成項の直和同型。 -/
def generatorIso : (extension φ).obj (BalancedTensor.generators A D M N) ≅
    BalancedTensor.generators A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) :=
  coproductIso φ (BalancedTensor.objectFamily A D M N) ≪≫
    Sigma.mapIso (fun x : D => tensorIso φ (M.obj (op x)) (N.obj x))

/-- 元と同じ対象対添字を使う関係項の直和同型。 -/
def relationIso : (extension φ).obj (BalancedTensor.relations A D M N) ≅
    BalancedTensor.relations A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) :=
  coproductIso φ (BalancedTensor.relationFamily A D M N) ≪≫
    Sigma.mapIso (fun xy : D × D => tripleIso φ (M.obj (op xy.2))
      (homObject A D xy.1 xy.2) (N.obj xy.1))

@[reassoc (attr := simp)]
lemma map_ι_generatorIso (x : D) :
    (extension φ).map (Sigma.ι (BalancedTensor.objectFamily A D M N) x) ≫
      (generatorIso φ D M N).hom =
        (tensorIso φ (M.obj (op x)) (N.obj x)).hom ≫
          Sigma.ι (BalancedTensor.objectFamily A' (DGBaseChange φ D)
            (rightModule φ D M) (leftModule φ D N)) x := by
  simp only [generatorIso, Iso.trans_hom, map_ι_coproductIso_assoc,
    Sigma.ι_mapIso_hom]

@[reassoc (attr := simp)]
lemma map_ι_relationIso (xy : D × D) :
    (extension φ).map (Sigma.ι (BalancedTensor.relationFamily A D M N) xy) ≫
      (relationIso φ D M N).hom =
        (tripleIso φ (M.obj (op xy.2)) (homObject A D xy.1 xy.2) (N.obj xy.1)).hom ≫
          Sigma.ι (BalancedTensor.relationFamily A' (DGBaseChange φ D)
            (rightModule φ D M) (leftModule φ D N)) xy := by
  simp only [relationIso, Iso.trans_hom, map_ι_coproductIso_assoc,
    Sigma.ι_mapIso_hom]

omit [Small.{u} D] in
@[reassoc]
lemma rightRelation_component (x y : D) :
    (extension φ).map (BalancedTensor.rightAction A D M x y ▷ N.obj x) ≫
        (tensorIso φ (M.obj (op x)) (N.obj x)).hom =
      (tripleIso φ (M.obj (op y)) (homObject A D x y) (N.obj x)).hom ≫
        BalancedTensor.rightAction A' (DGBaseChange φ D) (rightModule φ D M) x y ▷
          (extension φ).obj (N.obj x) := by
  have hn := tensorIso_naturality φ (BalancedTensor.rightAction A D M x y) (𝟙 (N.obj x))
  simp only [CategoryTheory.Functor.map_id, tensorHom_id] at hn
  rw [rightAction_comparison φ D M x y, comp_whiskerRight] at hn
  simpa only [tripleIso_hom, Category.assoc] using hn

omit [Small.{u} D] in
@[reassoc]
lemma leftRelation_component (x y : D) :
    (extension φ).map ((α_ (M.obj (op y)) (homObject A D x y) (N.obj x)).hom ≫
        M.obj (op y) ◁ BalancedTensor.leftAction A D N x y) ≫
      (tensorIso φ (M.obj (op y)) (N.obj y)).hom =
    (tripleIso φ (M.obj (op y)) (homObject A D x y) (N.obj x)).hom ≫
      (α_ ((extension φ).obj (M.obj (op y)))
        ((extension φ).obj (homObject A D x y)) ((extension φ).obj (N.obj x))).hom ≫
          (extension φ).obj (M.obj (op y)) ◁
            BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x y := by
  have hn := tensorIso_naturality φ (𝟙 (M.obj (op y))) (BalancedTensor.leftAction A D N x y)
  simp only [CategoryTheory.Functor.map_id, id_tensorHom] at hn
  rw [CategoryTheory.Functor.map_comp, Category.assoc, hn,
    leftAction_comparison φ D N x y, whiskerLeft_comp]
  have ha := congrArg (fun f => f ≫ (extension φ).obj (M.obj (op y)) ◁
      BalancedTensor.leftAction A' (DGBaseChange φ D) (leftModule φ D N) x y)
    (tensorIso_associator φ (M.obj (op y)) (homObject A D x y) (N.obj x)).symm
  simpa only [tripleIso_hom, Category.assoc] using ha

@[reassoc]
lemma relationLeft_square :
    (extension φ).map (BalancedTensor.relationLeft A D M N) ≫ (generatorIso φ D M N).hom =
      (relationIso φ D M N).hom ≫
        BalancedTensor.relationLeft A' (DGBaseChange φ D)
          (rightModule φ D M) (leftModule φ D N) := by
  apply (isColimitOfHasCoproductOfPreservesColimit (extension φ)
    (BalancedTensor.relationFamily A D M N)).hom_ext
  intro xy
  change (extension φ).map (Sigma.ι (BalancedTensor.relationFamily A D M N) xy.as) ≫ _ =
    (extension φ).map (Sigma.ι (BalancedTensor.relationFamily A D M N) xy.as) ≫ _
  rw [← CategoryTheory.Functor.map_comp_assoc, BalancedTensor.relationLeft,
    Sigma.ι_comp_desc, CategoryTheory.Functor.map_comp, Category.assoc, map_ι_generatorIso]
  rw [map_ι_relationIso_assoc, BalancedTensor.relationLeft, Sigma.ι_comp_desc]
  exact rightRelation_component_assoc φ D M N xy.as.1 xy.as.2 _

@[reassoc]
lemma relationRight_square :
    (extension φ).map (BalancedTensor.relationRight A D M N) ≫ (generatorIso φ D M N).hom =
      (relationIso φ D M N).hom ≫
        BalancedTensor.relationRight A' (DGBaseChange φ D)
          (rightModule φ D M) (leftModule φ D N) := by
  apply (isColimitOfHasCoproductOfPreservesColimit (extension φ)
    (BalancedTensor.relationFamily A D M N)).hom_ext
  intro xy
  change (extension φ).map (Sigma.ι (BalancedTensor.relationFamily A D M N) xy.as) ≫ _ =
    (extension φ).map (Sigma.ι (BalancedTensor.relationFamily A D M N) xy.as) ≫ _
  rw [← CategoryTheory.Functor.map_comp_assoc, BalancedTensor.relationRight,
    Sigma.ι_comp_desc]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [map_ι_generatorIso]
  rw [map_ι_relationIso_assoc, BalancedTensor.relationRight, Sigma.ι_comp_desc]
  have h := leftRelation_component_assoc φ D M N xy.as.1 xy.as.2
    (Sigma.ι (BalancedTensor.objectFamily A' (DGBaseChange φ D)
      (rightModule φ D M) (leftModule φ D N)) xy.as.2)
  simp only [CategoryTheory.Functor.map_comp, Category.assoc] at h
  convert h using 1; rfl

end SerrePositivity.DifferentialGraded.ScalarExtension

module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetNormalizationCubes
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomTargetCompositionTriangles
public import SerrePositivity.InfinityCategories.Derived.Gluing.IdentityCommaProjectionIntervalFamilies
/-!
概要：元終域の恒等 comma への全 Hom 入力は元 p・q と元左右鎖射影を保つ。
方針：像 Hom の射影則と元 comma 比較の射影則を合成し、実区間族へ移す。
規約：正規化の全時間の入力を変更しない。使われ方：元入力 fiber 内の補正道。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded DGNerve SSet KST.SConstruction
open scoped Simplicial
variable (R : Type u) [CommRing R]
  (C D E : Type (max (u + 1) v)) [DGCategory R C] [Small.{u} C]
  [DGCategory R D] [DGCategory R E] [Small.{u} E]
  (p : DGFunctor R C E) (q : DGFunctor R D E)
  (X Y : DGGluingObject R C D (dgHomGluingBimodule R C D E p q))
local notation "M" => dgHomGluingBimodule R C D E p q
local notation "IX" => dgGluingHomTargetIdentityCommaObject R C D E p q X
local notation "IY" => dgGluingHomTargetIdentityCommaObject R C D E p q Y
local notation "Q" => DGFunctorCommaObject R E E (DGFunctor.id E)

attribute [local irreducible] dgHomGluingBimodule

lemma dgGluingHomTargetIdentityCommaFunctor_source :
    (dgGluingHomTargetIdentityCommaFunctor R C D E p q).map X Y ≫
      dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) IX IY =
    dgGluingRightHomMap R C D M X Y ≫ q.map X.right Y.right := by
  change (dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
    dgGluingCommaImageHomMap R D E q _ _) ≫ _ = _
  dsimp only [dgGluingHomTargetIdentityCommaObject]
  rw [Category.assoc, dgGluingCommaImageHomMap_source, dgFunctorCommaImageHomMap,
    ← Category.assoc]
  erw [dgGluingHomTargetCommaHomMap_source]
  rfl

lemma dgGluingHomTargetIdentityCommaFunctor_replacement :
    (dgGluingHomTargetIdentityCommaFunctor R C D E p q).map X Y ≫
      dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) IX IY =
    dgGluingLeftHomMap R C D M X Y ≫ p.map X.left Y.left := by
  change (dgGluingHomTargetCommaHomMap R C D E p q X Y ≫
    dgGluingCommaImageHomMap R D E q _ _) ≫ _ = _
  dsimp only [dgGluingHomTargetIdentityCommaObject]
  rw [Category.assoc, dgGluingCommaImageHomMap_replacement]
  exact dgGluingHomTargetCommaHomMap_replacement R C D E p q X Y

lemma dgGluingHomTargetNormalizationHomInput_source :
    dgGluingHomTargetNormalizationHomInput R C D E p q X Y ≫
      pinchedHomChainMap (D := Q) (E := E)
        (dgFunctorCommaSourceHomMap R E E (DGFunctor.id E) IX IY) =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) ≫
      dgGluingHomTargetRightCoefficientInput R C D E p q X Y := by
  rw [dgGluingHomTargetNormalizationHomInput, Category.assoc,
    ← pinchedHomChainMap_comp, dgGluingHomTargetIdentityCommaFunctor_source]
  have hn := (dgGluingComplexPinchedModelInverse_naturality
    (C := DGGluingObject R C D M) (D := E)
    (x := X) (y := Y) (x' := q.obj X.right) (y' := q.obj Y.right)
    (dgGluingRightHomMap R C D M X Y ≫ q.map X.right Y.right)).symm
  exact hn.trans (by
    rw [complexPinchedMap_comp, Category.assoc]
    rfl)

lemma dgGluingHomTargetNormalizationHomInput_replacement :
    dgGluingHomTargetNormalizationHomInput R C D E p q X Y ≫
      pinchedHomChainMap (D := Q) (E := E)
        (dgFunctorCommaReplacementHomMap R E E (DGFunctor.id E) IX IY) =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) ≫
      dgGluingHomTargetLeftCoefficientInput R C D E p q X Y := by
  rw [dgGluingHomTargetNormalizationHomInput, Category.assoc,
    ← pinchedHomChainMap_comp, dgGluingHomTargetIdentityCommaFunctor_replacement]
  have hn := (dgGluingComplexPinchedModelInverse_naturality
    (C := DGGluingObject R C D M) (D := E)
    (x := X) (y := Y) (x' := p.obj X.left) (y' := p.obj Y.left)
    (dgGluingLeftHomMap R C D M X Y ≫ p.map X.left Y.left)).symm
  exact hn.trans (by
    rw [complexPinchedMap_comp, Category.assoc]
    rfl)

lemma dgGluingHomTargetNormalizationSourceIntervalFamily :
    dgGluingIdentityCommaSourceIntervalFamily.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingRightHomMap R C D M X Y) ≫
      dgGluingHomTargetRightIntervalInput R C D E p q X Y := by
  have hc := dgGluingIdentityCommaSourceIntervalFamily_chain.{u, max (u + 1) v}
    R E IX IY (dgGluingHomTargetNormalizationHomInput R C D E p q X Y)
  have ht := congrArg (fun k => k ≫ pinchedHomToIntervalMappingSpace (X := dgNerve R E)
      (Simplex.vertex (q.obj X.right)) (Simplex.vertex (q.obj Y.right)))
    (dgGluingHomTargetNormalizationHomInput_source R C D E p q X Y)
  exact hc.trans (ht.trans (Category.assoc _ _ _))

lemma dgGluingHomTargetNormalizationReplacementIntervalFamily :
    dgGluingIdentityCommaReplacementIntervalFamily.{u, max (u + 1) v} R E IX IY
      (dgGluingHomTargetNormalizationHomInput R C D E p q X Y) =
    complexPinchedMap.{u, max (u + 1) v} (dgGluingLeftHomMap R C D M X Y) ≫
      dgGluingHomTargetLeftIntervalInput R C D E p q X Y := by
  have ht := congrArg (fun k => k ≫ pinchedHomToIntervalMappingSpace (X := dgNerve R E)
      (Simplex.vertex (p.obj X.left)) (Simplex.vertex (p.obj Y.left)))
    (dgGluingHomTargetNormalizationHomInput_replacement R C D E p q X Y)
  exact ht.trans (Category.assoc _ _ _)

end SerrePositivity.InfinityCategories

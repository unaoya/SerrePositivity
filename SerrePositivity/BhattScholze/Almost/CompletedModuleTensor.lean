module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.CompletionMonoidal
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.HeartFullyFaithful
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.Resolutions.SemifreeKProjective

/-! # 完備導来テンソルの模型比較

## 概要
離散入力の完備導来テンソルを、導来頂点の自由解像度と有界上側の代数模型で比較する。
BS 著者版 Lemma 10.3 と Proposition 10.4 の間で使う。

## 方針
両模型に同じ自由解像度を指定し、導来完備化を同じ複体に適用する。

## 規約
次数はコホモロジー次数。代数の標準因子写像は解像度上の単位写像で比較する。

## 使われ方
BS 著者版 Remark 10.7 の係数環の比較。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Almost

open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial
open InfinityCategories DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]

/-- 導来圏の半自由代表を指定する頂点。 -/
abbrev DVertex := (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory R) _⦋0⦌

/-- 頂点の半自由複体のテンソルを導来 p 完備化して頂点に戻す。 -/
def completedModuleTensor (p : ℕ) (A : Type u) [CommRing A] (X Y : DVertex A) : DVertex A :=
  let C := DerivedCategory.Q.obj (cochainTensor (X.obj 0).val (Y.obj 0).val)
  ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence A).inverse.obj
    ((derivedComplexCompletionFunctor A (p : A)).obj C)).pt

/-- 離散頂点と同じ関手的自由解像度を有界上側の導来模型に指定する。 -/
def moduleHeartProjectiveModel (M : ModuleCat.{u} R) :
    BoundedAboveDerivedModel ((boundedAboveDerivedSingleFunctor.obj M).obj) where
  complex := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).obj M
  bound := 0
  bounded := (CochainComplex.isStrictlyLE_iff _ _).mpr (fun k hk =>
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution_isZero R M k hk)
  projective i := by
    let := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution_free R M i
    infer_instance
  iso := by
    letI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation_quasiIso R M
    exact asIso (DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation R M))

/-- 有界上側の完備テンソルを二つの自由解像度のテンソルで計算する。 -/
def completedTensorResolutionIso (a : R) (M N : ModuleCat.{u} R) :
    ((boundedAboveDerivedCompletionFunctor R a).obj
      (boundedAboveDerivedTensor.obj (boundedAboveDerivedSingleFunctor.obj M,
        boundedAboveDerivedSingleFunctor.obj N))).obj ≅
      (derivedComplexCompletionFunctor R a).obj
        (DerivedCategory.Q.obj (cochainTensor ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).obj M)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).obj N))) :=
  (derivedComplexCompletionFunctor R a).mapIso
    (boundedAboveDerivedTensorModelIso _ _
      (moduleHeartProjectiveModel R M) (moduleHeartProjectiveModel R N))

/-- BS 著者版 Lemma 10.3 の完備代数テンソルの底を導来頂点で計算する。 -/
def completedTensorAlgebraVertexIso (p : ℕ) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] :
    (boundedAboveCompletedTensorAlgebra R (p : R) S T).X.obj ≅
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj
        ⟨completedModuleTensor p R (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartVertex R (ModuleCat.of R S))
          (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.ChainComplexes.moduleHeartVertex R (ModuleCat.of R T))⟩ := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R
  exact completedTensorResolutionIso R (p : R) (ModuleCat.of R S) (ModuleCat.of R T) ≪≫
    (e.counitIso.app _).symm

/-- 自由解像度での計算は二つの加群の射に関して自然。 -/
theorem completedTensorResolutionIso_naturality (a : R) {M M' N N' : ModuleCat.{u} R}
    (f : M ⟶ M') (g : N ⟶ N') :
    ((boundedAboveDerivedCompletionFunctor R a).map
      (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom
        (boundedAboveDerivedSingleFunctor.map f) (boundedAboveDerivedSingleFunctor.map g)))).hom ≫
      (completedTensorResolutionIso R a M' N').hom =
    (completedTensorResolutionIso R a M N).hom ≫
      (derivedComplexCompletionFunctor R a).map (DerivedCategory.Q.map
        (cochainTensorMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).map f)
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).map g))) := by
  have represent {A B : ModuleCat.{u} R} (h : A ⟶ B) :
      DerivedCategory.Q.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).map h) ≫
        (moduleHeartProjectiveModel R B).iso.hom =
      (moduleHeartProjectiveModel R A).iso.hom ≫ (boundedAboveDerivedSingleFunctor.map h).hom := by
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ =
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentationNat R).naturality]
  change (derivedComplexCompletionFunctor R a).map _ ≫
      (derivedComplexCompletionFunctor R a).map _ =
    (derivedComplexCompletionFunctor R a).map _ ≫ (derivedComplexCompletionFunctor R a).map _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (derivedComplexCompletionFunctor R a).map
    (boundedAboveDerivedTensorModelIso_naturality
      (moduleHeartProjectiveModel R M) (moduleHeartProjectiveModel R M')
      (moduleHeartProjectiveModel R N) (moduleHeartProjectiveModel R N')
      (boundedAboveDerivedSingleFunctor.map f) (boundedAboveDerivedSingleFunctor.map g)
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).map f) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).map g)
      (represent f) (represent g))

open MonoidalCategory

/-- 完備代数テンソルへの左因子写像は、右因子の単位をテンソルして得られる。 -/
lemma completedTensorAlgebraLeft_resolution (a : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (uT : cochainTensorUnit (R := R) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).obj (ModuleCat.of R T))
    (huT : DerivedCategory.Q.map uT ≫ (moduleHeartProjectiveModel R (ModuleCat.of R T)).iso.hom =
      (boundedAboveDerivedAlgebraUnit (R := R) T).hom) :
    (boundedAboveCompletedTensorAlgebraLeft R a S T).hom.hom.hom ≫
      (completedTensorResolutionIso R a (ModuleCat.of R S) (ModuleCat.of R T)).hom =
    (moduleHeartProjectiveModel R (ModuleCat.of R S)).iso.inv ≫
      DerivedCategory.Q.map (cochainTensorRightUnitor
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).obj (ModuleCat.of R S))).inv ≫
      DerivedCategory.Q.map (cochainTensorMap
        (𝟙 ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).obj (ModuleCat.of R S))) uT) ≫
      (derivedComplexCompletionUnit R a).app _ := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)
  let Y := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)
  let P := moduleHeartProjectiveModel R (ModuleCat.of R S)
  let Q := moduleHeartProjectiveModel R (ModuleCat.of R T)
  let U := boundedAboveDerivedTensorUnit (R := R)
  let UP := boundedAboveDerivedTensorUnitModel (R := R)
  let C := derivedComplexCompletionFunctor R a
  let η := derivedComplexCompletionUnit R a
  let f := boundedAboveDerivedAlgebraUnit (R := R) T
  let k := cochainTensorMap (𝟙 P.complex) uT
  let modelIso := boundedAboveDerivedTensorModelIso X Y P Q
  have hn := boundedAboveDerivedTensorModelIso_naturality P P UP Q
    (𝟙 X) f (𝟙 P.complex) uT (by
      change DerivedCategory.Q.map (𝟙 P.complex) ≫ P.iso.hom = P.iso.hom ≫ 𝟙 X.obj
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])
    (by simpa [UP, boundedAboveDerivedTensorUnitModel] using huT)
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom (𝟙 X) f)).hom ≫
    modelIso.hom = (boundedAboveDerivedTensorModelIso X U P UP).hom ≫
      DerivedCategory.Q.map k at hn
  have hunit := boundedAboveDerivedRightUnitor_models X P
  have hunit' :
      (boundedAboveDerivedTensorRightUnitor X).inv.hom ≫
        (boundedAboveDerivedTensorModelIso X U P UP).hom =
        P.iso.inv ≫ DerivedCategory.Q.map (cochainTensorRightUnitor P.complex).inv := by
    calc
      _ = (boundedAboveDerivedTensorRightUnitor X).inv.hom ≫
        (boundedAboveDerivedTensorRightUnitor X).hom.hom ≫ P.iso.inv ≫
          DerivedCategory.Q.map (cochainTensorRightUnitor P.complex).inv := by
            rw [hunit]
            simp [← Functor.map_comp]
            rfl
      _ = _ := by
        change (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensorRightUnitor X)).inv ≫
          (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensorRightUnitor X)).hom ≫
          P.iso.inv ≫ _ = _
        simp
  have hl : (boundedAboveCompletedTensorAlgebraLeft R a S T).hom.hom.hom =
      (boundedAboveDerivedTensorRightUnitor X).inv.hom ≫
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom (𝟙 X) f)).hom ≫ η.app _ := by
    change ((boundedAboveDerivedTensorAlgebraLeft S T).hom.hom ≫
      (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedTensorAlgebra S T)).hom.hom).hom = _
    rw [ObjectProperty.FullSubcategory.comp_hom, boundedAboveCompletionAlgebraUnit_hom,
      boundedAboveDerivedTensorAlgebraLeft_hom, ObjectProperty.FullSubcategory.comp_hom,
      Category.assoc]
    rfl
  change (boundedAboveCompletedTensorAlgebraLeft R a S T).hom.hom.hom ≫ C.map modelIso.hom =
    P.iso.inv ≫ DerivedCategory.Q.map (cochainTensorRightUnitor P.complex).inv ≫
      DerivedCategory.Q.map k ≫ η.app _
  rw [hl, Category.assoc, Category.assoc, ← η.naturality, Functor.id_map,
    ← Category.assoc ((boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom (𝟙 X) f)).hom),
    hn]
  simp only [Category.assoc, reassoc_of% hunit']
  rfl

/-- 代数の単位は次数零の単位複体から自由解像度への鎖写像で表せる。 -/
theorem exists_moduleHeartUnitLift (T : Type u) [CommRing T] [Algebra R T] :
    ∃ uT : cochainTensorUnit (R := R) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).obj (ModuleCat.of R T),
      DerivedCategory.Q.map uT ≫ (moduleHeartProjectiveModel R (ModuleCat.of R T)).iso.hom =
        (boundedAboveDerivedAlgebraUnit (R := R) T).hom := by
  let U := boundedAboveDerivedTensorUnitModel (R := R)
  let P := moduleHeartProjectiveModel R (ModuleCat.of R T)
  have h := U.map_naturality P (boundedAboveDerivedAlgebraUnit (R := R) T).hom
  exact ⟨_, by simpa [U, boundedAboveDerivedTensorUnitModel] using h⟩

/-- 完備代数テンソルへの右因子写像は、左因子の単位をテンソルして得られる。 -/
lemma completedTensorAlgebraRight_resolution (a : R) (S T : Type u)
    [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (uT : cochainTensorUnit (R := R) ⟶ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).obj (ModuleCat.of R T))
    (huT : DerivedCategory.Q.map uT ≫ (moduleHeartProjectiveModel R (ModuleCat.of R T)).iso.hom =
      (boundedAboveDerivedAlgebraUnit (R := R) T).hom) :
    (boundedAboveCompletedTensorAlgebraRight R a T S).hom.hom.hom ≫
      (completedTensorResolutionIso R a (ModuleCat.of R T) (ModuleCat.of R S)).hom =
    (moduleHeartProjectiveModel R (ModuleCat.of R S)).iso.inv ≫
      DerivedCategory.Q.map (cochainTensorLeftUnitor
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).obj (ModuleCat.of R S))).inv ≫
      DerivedCategory.Q.map (cochainTensorMap
        uT (𝟙 ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution R).obj (ModuleCat.of R S)))) ≫
      (derivedComplexCompletionUnit R a).app _ := by
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R S)
  let Y := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of R T)
  let P := moduleHeartProjectiveModel R (ModuleCat.of R S)
  let Q := moduleHeartProjectiveModel R (ModuleCat.of R T)
  let U := boundedAboveDerivedTensorUnit (R := R)
  let UP := boundedAboveDerivedTensorUnitModel (R := R)
  let C := derivedComplexCompletionFunctor R a
  let η := derivedComplexCompletionUnit R a
  let f := boundedAboveDerivedAlgebraUnit (R := R) T
  let k := cochainTensorMap uT (𝟙 P.complex)
  let modelIso := boundedAboveDerivedTensorModelIso Y X Q P
  have hn := boundedAboveDerivedTensorModelIso_naturality UP Q P P
    f (𝟙 X) uT (𝟙 P.complex) (by simpa [UP, boundedAboveDerivedTensorUnitModel] using huT)
    (by
      change DerivedCategory.Q.map (𝟙 P.complex) ≫ P.iso.hom = P.iso.hom ≫ 𝟙 X.obj
      rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id])
  change (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom f (𝟙 X))).hom ≫
    modelIso.hom = (boundedAboveDerivedTensorModelIso U X UP P).hom ≫
      DerivedCategory.Q.map k at hn
  have hunit := boundedAboveDerivedLeftUnitor_models X P
  have hunit' :
      (boundedAboveDerivedTensorLeftUnitor X).inv.hom ≫
        (boundedAboveDerivedTensorModelIso U X UP P).hom =
        P.iso.inv ≫ DerivedCategory.Q.map (cochainTensorLeftUnitor P.complex).inv := by
    calc
      _ = (boundedAboveDerivedTensorLeftUnitor X).inv.hom ≫
        (boundedAboveDerivedTensorLeftUnitor X).hom.hom ≫ P.iso.inv ≫
          DerivedCategory.Q.map (cochainTensorLeftUnitor P.complex).inv := by
            rw [hunit]
            simp [← Functor.map_comp]
            rfl
      _ = _ := by
        change (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensorLeftUnitor X)).inv ≫
          (DerivedCategory.Minus.ι.mapIso (boundedAboveDerivedTensorLeftUnitor X)).hom ≫
          P.iso.inv ≫ _ = _
        simp
  have hl : (boundedAboveCompletedTensorAlgebraRight R a T S).hom.hom.hom =
      (boundedAboveDerivedTensorLeftUnitor X).inv.hom ≫
        (boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom f (𝟙 X))).hom ≫ η.app _ := by
    change ((boundedAboveDerivedTensorAlgebraRight T S).hom.hom ≫
      (boundedAboveCompletionAlgebraUnit R a
        (boundedAboveDerivedTensorAlgebra T S)).hom.hom).hom = _
    rw [ObjectProperty.FullSubcategory.comp_hom, boundedAboveCompletionAlgebraUnit_hom,
      boundedAboveDerivedTensorAlgebraRight_hom, ObjectProperty.FullSubcategory.comp_hom,
      Category.assoc]
    rfl
  change (boundedAboveCompletedTensorAlgebraRight R a T S).hom.hom.hom ≫ C.map modelIso.hom =
    P.iso.inv ≫ DerivedCategory.Q.map (cochainTensorLeftUnitor P.complex).inv ≫
      DerivedCategory.Q.map k ≫ η.app _
  rw [hl, Category.assoc, Category.assoc, ← η.naturality, Functor.id_map,
    ← Category.assoc ((boundedAboveDerivedTensor.map (CategoryTheory.Prod.mkHom f (𝟙 X))).hom),
    hn]
  simp only [Category.assoc, reassoc_of% hunit']
  rfl


section Boundedness

variable {R}

/-- 有界上側の射影模型を、頂点が指定する半自由代表へ擬同型で送る。 -/
private theorem exists_projectiveModelToVertex
    (X : DVertex R)
    (P : BoundedAboveDerivedModel ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj ⟨X⟩)) :
    ∃ f : P.complex ⟶ (X.obj 0).val, QuasiIso f := by
  let e := P.iso ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedVertexLocalizationIso X
  obtain ⟨f, hf⟩ := exists_cochainMap_of_isKProjective e.hom
  refine ⟨f, (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) f).mp ?_⟩
  rw [hf]
  infer_instance

/-- 完備導来テンソルのコホモロジーの上界は、両入力の上界の和で抑えられる。 -/
theorem completedModuleTensor_isLE (p : ℕ) (X Y : DVertex R) (i j : ℤ)
    (hX : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj ⟨X⟩).IsLE i)
    (hY : ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj ⟨Y⟩).IsLE j) :
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R).functor.obj
      ⟨completedModuleTensor p R X Y⟩).IsLE (i + j) := by
  let e := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence R
  have := hX
  have := hY
  let P := BoundedAboveDerivedModel.ofIsLE (e.functor.obj ⟨X⟩) i
  let Q := BoundedAboveDerivedModel.ofIsLE (e.functor.obj ⟨Y⟩) j
  obtain ⟨f, hf⟩ := exists_projectiveModelToVertex X P
  obtain ⟨g, hg⟩ := exists_projectiveModelToVertex Y Q
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective R (X.obj 0).property
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexSemifree_isKProjective R (Y.obj 0).property
  have := cochainTensorMap_quasiIso_of_KProjective f g
  let h := asIso (DerivedCategory.Q.map (cochainTensorMap f g))
  let X' : DerivedCategory.Minus (ModuleCat R) := ⟨_, ⟨i, hX⟩⟩
  let Y' : DerivedCategory.Minus (ModuleCat R) := ⟨_, ⟨j, hY⟩⟩
  have hXY : ((boundedAboveDerivedTensor.obj (X', Y')).obj).IsLE (i + j) :=
    boundedAboveDerivedTensor_isLE_add X' Y' i j
  let hcomp := (derivedComplexCompletionFunctor R (p : R)).mapIso
    (boundedAboveDerivedTensorModelIso X' Y' P Q ≪≫ h)
  have := derivedComplexCompletionFunctor_isLE R (p : R) _ _ hXY
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (hcomp ≪≫ (e.counitIso.app _).symm) (i + j)

end Boundedness

end SerrePositivity.BhattScholze.Almost

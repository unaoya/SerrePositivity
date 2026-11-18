module

public import SerrePositivity.EInfinity.Modules.TensorHomAdjunction
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounit
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# 同じ正規化単体を使う加群の source frame の全族

概要：M10 の標準単体テンソルと元の加群への augmentation を全関手にする。
方針：既存のテンソル作用・AW 余単位・左単位子を貼り合わせる。
規約：HA §1.3.4、Reedy 条件は実モデルのもとで別に確認する。
使われ方：同じ dg Hom とモデル frame Hom の全標的自然な比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ標準単体テンソルは全加群射と全単体作用素の族を持つ。
方針：既存の二つのテンソル射の交換を評価で照合する。
規約：HA §1.3.4、元の加群を保持。使われ方：具体的 source frame の全族。 -/
def moduleTensorSimplicesFunctor :
    ModuleCategory A D ⥤ (SimplexCategory ⥤ ModuleCategory A D) where
  obj M := SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A ⋙
    tensorModuleFunctor (ForgetEnrichment.to (Complex A) M)
  map f := {
    app n := moduleTensorLeftMap A D
      ((BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n)) f
    naturality n m θ := by
      apply moduleMorphism_ext
      intro x
      change (moduleEvaluation A D x).map
          (tensorModuleMap ((BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map θ))
            (ForgetEnrichment.to (Complex A) _) ≫ moduleTensorLeftMap A D _ f) =
        (moduleEvaluation A D x).map
          (moduleTensorLeftMap A D _ f ≫
            tensorModuleMap ((BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map θ))
              (ForgetEnrichment.to (Complex A) _))
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
        tensorModuleMap_eval, tensorModuleMap_eval,
        moduleTensorLeftMap_eval, moduleTensorLeftMap_eval]
      simp only [tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
      exact congrArg
        (fun z => (BarrattEccles.normalizedFunctor A).map (SSet.stdSimplex.map θ) ⊗ₘ z)
        (Category.comp_id ((moduleEvaluation A D x).map f)).symm }
  map_id M := by
    apply NatTrans.ext
    funext n
    exact (moduleTensorLeftFunctor A D
      ((BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n))).map_id M
  map_comp f g := by
    apply NatTrans.ext
    funext n
    exact (moduleTensorLeftFunctor A D
      ((BarrattEccles.normalizedFunctor A).obj (SSet.stdSimplex.obj n))).map_comp f g

/-- 概要：同じ source frame の対象を評価すると元の単体複体の左テンソル。
方針：関手の合成を評価する。
規約：HA §1.3.4、全次元。使われ方：同じ全 Hom との転置。 -/
lemma moduleTensorSimplices_obj_eval (M : ModuleCategory A D) (n : SimplexCategory) (x : D) :
    (moduleEvaluation A D x).obj (((moduleTensorSimplicesFunctor A D).obj M).obj n) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A (SSet.stdSimplex.obj n) ⊗
        (moduleEvaluation A D x).obj M := rfl

/-- 概要：同じ全標的の作用は単位と元の加群射のテンソル。
方針：既存のテンソル加群射を評価する。
規約：HA §1.3.4、元の射。使われ方：全族の自然性の照合。 -/
lemma moduleTensorSimplices_map_eval {M N : ModuleCategory A D} (f : M ⟶ N)
    (n : SimplexCategory) (x : D) :
    (moduleEvaluation A D x).map (((moduleTensorSimplicesFunctor A D).map f).app n) =
      𝟙 (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochains A (SSet.stdSimplex.obj n)) ⊗ₘ
        (moduleEvaluation A D x).map f :=
  moduleTensorLeftMap_eval A D _ f x

/-- 概要：同じ AW 余単位と左単位子は元の加群への全単体 augmentation。
方針：余単位の自然性を元の係数テンソル関手で送る。
規約：HA §1.3.4、同じ元の加群。使われ方：source frame の比較の底。 -/
def moduleTensorSimplicesAugmentation (M : ModuleCategory A D) :
    (moduleTensorSimplicesFunctor A D).obj M ⟶ (Functor.const SimplexCategory).obj M where
  app n := tensorModuleMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n))
    (ForgetEnrichment.to (Complex A) M) ≫
      (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom
  naturality n m f := by
    let L := tensorModuleFunctor (ForgetEnrichment.to (Complex A) M)
    change L.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainMap A (SSet.stdSimplex.map f)) ≫
        (L.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj m)) ≫ _) =
      (L.map (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n)) ≫ _) ≫ 𝟙 M
    rw [Category.comp_id, ← Category.assoc, ← L.map_comp]
    exact congrArg (fun z => L.map z ≫
      (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom)
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_natural A (SSet.stdSimplex.map f))

/-- 概要：同じ augmentation の評価は元の AW 余単位をテンソルした後の左単位子。
方針：既存の二つの射の評価式を合成する。
規約：HA §1.3.4、射自身の式。使われ方：元の比較の回収。 -/
lemma moduleTensorSimplicesAugmentation_eval (M : ModuleCategory A D)
    (n : SimplexCategory) (x : D) :
    (moduleEvaluation A D x).map ((moduleTensorSimplicesAugmentation A D M).app n) =
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n) ⊗ₘ
        𝟙 ((moduleEvaluation A D x).obj M)) ≫ (λ_ ((moduleEvaluation A D x).obj M)).hom := by
  change (moduleEvaluation A D x).map
      (tensorModuleMap (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n))
        (ForgetEnrichment.to (Complex A) M) ≫
          (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom) = _
  rw [CategoryTheory.Functor.map_comp, tensorModuleMap_eval, moduleTensorUnitIso_hom_eval]
  rfl

/-- 概要：同じ augmentation は全ての元の加群射について自然。
方針：テンソル射の交換と左単位子の自然性を使う。
規約：HA §1.3.4、全対象族。使われ方：モデル frame との全自然比較。 -/
def moduleTensorSimplicesAugmentationFamily :
    moduleTensorSimplicesFunctor A D ⟶ Functor.const SimplexCategory where
  app := moduleTensorSimplicesAugmentation A D
  naturality M N f := by
    apply NatTrans.ext
    funext n
    apply moduleMorphism_ext
    intro x
    let E := moduleEvaluation A D x
    let ε := _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n)
    change E.map ((((moduleTensorSimplicesFunctor A D).map f).app n) ≫
        (moduleTensorSimplicesAugmentation A D N).app n) =
      E.map ((moduleTensorSimplicesAugmentation A D M).app n ≫ f)
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      moduleTensorSimplices_map_eval, moduleTensorSimplicesAugmentation_eval,
      moduleTensorSimplicesAugmentation_eval]
    have h : (𝟙 (𝟙_ (Complex A)) ⊗ₘ E.map f) ≫ (λ_ (E.obj N)).hom =
        (λ_ (E.obj M)).hom ≫ E.map f := leftUnitor_naturality (E.map f)
    calc
      _ = (ε ⊗ₘ 𝟙 (E.obj M)) ≫
          ((𝟙 (𝟙_ (Complex A)) ⊗ₘ E.map f) ≫ (λ_ (E.obj N)).hom) := by
        simp only [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp,
          Category.comp_id]
        exact congrArg (fun z => (z ⊗ₘ E.map f) ≫ (λ_ (E.obj N)).hom)
          (Category.comp_id ε).symm
      _ = (ε ⊗ₘ 𝟙 (E.obj M)) ≫ ((λ_ (E.obj M)).hom ≫ E.map f) :=
        congrArg (fun z => (ε ⊗ₘ 𝟙 (E.obj M)) ≫ z) h
      _ = _ := (Category.assoc _ _ _).symm

end SerrePositivity.EInfinity.Modules

module
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtensionPresentation

/-! # 相対 balanced tensor の underived 係数変更同型

生成項・関係項の添字は同じ対象および同じ対象対に固定する。
係数環の平坦性は使わず、直和と coequalizer の保存から同型を作る。
-/
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

/-- 二つの関係射を含む coequalizer 図式全体の同型。 -/
def balancedPresentationIso :
    parallelPair ((extension φ).map (BalancedTensor.relationLeft A D M N))
      ((extension φ).map (BalancedTensor.relationRight A D M N)) ≅
    parallelPair
      (BalancedTensor.relationLeft A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N))
      (BalancedTensor.relationRight A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N)) :=
  parallelPairIso _ _ _ _ (relationIso φ D M N) (generatorIso φ D M N)
    (relationLeft_square φ D M N) (relationRight_square φ D M N)

/-- 任意の環準同型について、相対 tensor と係数拡大は可換する。 -/
def balancedIso : (extension φ).obj (BalancedTensor.obj A D M N) ≅
    BalancedTensor.obj A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) :=
  coequalizerIso φ (BalancedTensor.relationLeft A D M N) (BalancedTensor.relationRight A D M N) ≪≫
    HasColimit.isoOfNatIso (balancedPresentationIso φ D M N)

@[reassoc]
lemma balancedIso_projection :
    (extension φ).map (BalancedTensor.projection A D M N) ≫ (balancedIso φ D M N).hom =
      (generatorIso φ D M N).hom ≫
        BalancedTensor.projection A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) := by
  rw [balancedIso, Iso.trans_hom]
  change (extension φ).map (coequalizer.π _ _) ≫ (coequalizerIso φ _ _).hom ≫ _ = _
  rw [map_π_coequalizerIso_assoc]
  exact HasColimit.ι_isoOfNatIso_hom (balancedPresentationIso φ D M N) WalkingParallelPair.one

@[reassoc (attr := simp)]
lemma balancedIso_ι (x : D) :
    (extension φ).map (BalancedTensor.ι A D M N x) ≫ (balancedIso φ D M N).hom =
      (tensorIso φ (M.obj (op x)) (N.obj x)).hom ≫
        BalancedTensor.ι A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) x := by
  rw [BalancedTensor.ι, CategoryTheory.Functor.map_comp, Category.assoc,
    balancedIso_projection, ← Category.assoc, map_ι_generatorIso, Category.assoc]
  rfl

@[reassoc (attr := simp)]
lemma balancedIso_inv_ι (x : D) :
    BalancedTensor.ι A' (DGBaseChange φ D) (rightModule φ D M) (leftModule φ D N) x ≫
      (balancedIso φ D M N).inv =
      (tensorIso φ (M.obj (op x)) (N.obj x)).inv ≫
        (extension φ).map (BalancedTensor.ι A D M N x) := by
  have h := congrArg (fun t => (tensorIso φ (M.obj (op x)) (N.obj x)).inv ≫ t ≫
    (balancedIso φ D M N).inv) (balancedIso_ι φ D M N x)
  simp only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc, Category.comp_id] at h
  exact h.symm

/-- 係数変更後も、元の各対象の生成項の像が射を決める。 -/
lemma extendedBalanced_hom_ext {T : Complex A'}
    {f g : (extension φ).obj (BalancedTensor.obj A D M N) ⟶ T}
    (h : ∀ x : D, (extension φ).map (BalancedTensor.ι A D M N x) ≫ f =
      (extension φ).map (BalancedTensor.ι A D M N x) ≫ g) : f = g := by
  let : Epi ((extension φ).map (BalancedTensor.projection A D M N)) := by
    change Epi ((extension φ).map (coequalizer.π
      (BalancedTensor.relationLeft A D M N) (BalancedTensor.relationRight A D M N)))
    infer_instance
  apply (cancel_epi ((extension φ).map (BalancedTensor.projection A D M N))).1
  apply (isColimitOfHasCoproductOfPreservesColimit (extension φ)
    (BalancedTensor.objectFamily A D M N)).hom_ext
  intro x
  have hh := h x.as
  simp only [BalancedTensor.ι, CategoryTheory.Functor.map_comp, Category.assoc] at hh
  convert hh using 1 <;> rfl

end SerrePositivity.DifferentialGraded.ScalarExtension

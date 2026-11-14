module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGIntegerCoefficientTensor
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ChainTensorVanishing
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.AlexanderWhitney

/-!
概要：任意の宇宙の整数鎖テンソルの各全次数を同宇宙の係数環のテンソルへ比較する。
方針：既存の整数係数移送のテンソル同型と余積比較を合成する。
規約：元の i+j=n の余積と全射を保つ。複体への組立ては微分の照合後に行う。
使われ方：HA 1.2.4、G10 の EZ 比較と負次数テンソル底変換の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ)

/-- 元の整数テンソルの全次数の余積添字。 -/
abbrev integerTensorSummand (n : ℕ) :=
  fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} => integerTensor (K.X ij.val.1) (L.X ij.val.2)

/-- 移した全次数と、移した両因子の全次数との指定同型。 -/
def integerCoefficientTensorXIso (n : ℕ) :
    (integerCoefficientModuleFunctor.{u}).obj ((chainIntegerTensor K L).X n) ≅
      (HomologicalComplex.tensorObj (((integerCoefficientModuleFunctor.{u}).mapHomologicalComplex (.down ℕ)).obj K)
        (((integerCoefficientModuleFunctor.{u}).mapHomologicalComplex (.down ℕ)).obj L)).X n :=
  (asIso (sigmaComparison (integerCoefficientModuleFunctor.{u}) (integerTensorSummand K L n))).symm ≪≫
    Sigma.mapIso (fun ij => (integerCoefficientTensorIso (K.X ij.val.1) (L.X ij.val.2)).symm)

/-- 指定同型は各二重次数の既存テンソル比較の逆を使う。 -/
@[reassoc]
theorem map_ι_integerCoefficientTensorXIso (i j n : ℕ) (h : i + j = n) :
    (integerCoefficientModuleFunctor.{u}).map (ιMapBifunctor K L integerTensorBifunctor (.down ℕ) i j n h) ≫
        (integerCoefficientTensorXIso K L n).hom =
      (integerCoefficientTensorIso (K.X i) (L.X j)).inv ≫
        ιTensorObj (((integerCoefficientModuleFunctor.{u}).mapHomologicalComplex (.down ℕ)).obj K)
          (((integerCoefficientModuleFunctor.{u}).mapHomologicalComplex (.down ℕ)).obj L) i j n h := by
  change (integerCoefficientModuleFunctor.{u}).map (Sigma.ι (integerTensorSummand K L n) ⟨(i,j), h⟩) ≫
    (inv (sigmaComparison (integerCoefficientModuleFunctor.{u}) (integerTensorSummand K L n)) ≫
      (Sigma.mapIso (fun ij : {ij : ℕ × ℕ // ij.1 + ij.2 = n} =>
        (integerCoefficientTensorIso (K.X ij.val.1) (L.X ij.val.2)).symm)).hom) = _
  rw [← Category.assoc, map_ι_comp_inv_sigmaComparison, Sigma.ι_mapIso_hom]
  rfl

/-- 係数テンソルの逆比較も両変数の射に自然。 -/
@[reassoc]
theorem integerCoefficientTensorInv_naturality
    {M M' N N' : ModuleCat.{u} ℤ} (f : M ⟶ M') (g : N ⟶ N') :
    integerCoefficientModuleFunctor.map (integerTensorMap f g) ≫
        (integerCoefficientTensorIso M' N').inv =
      (integerCoefficientTensorIso M N).inv ≫
        (integerCoefficientModuleFunctor.map f ⊗ₘ integerCoefficientModuleFunctor.map g) := by
  apply (cancel_mono (integerCoefficientTensorIso M' N').hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [integerCoefficientTensorComparison_naturality]
  exact (integerCoefficientTensorIso M N).inv_hom_id_assoc _ |>.symm

/-- 全次数比較は元の二つの鎖写像に自然。 -/
theorem integerCoefficientTensorXIso_naturality
    {K K' L L' : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ K') (g : L ⟶ L') (n : ℕ) :
    integerCoefficientModuleFunctor.map ((chainIntegerTensorMap f g).f n) ≫
        (integerCoefficientTensorXIso K' L' n).hom =
      (integerCoefficientTensorXIso K L n).hom ≫
        (HomologicalComplex.tensorHom
          ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).map f)
          ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).map g)).f n := by
  apply (cancel_epi (sigmaComparison integerCoefficientModuleFunctor
    (integerTensorSummand K L n))).1
  apply Sigma.hom_ext
  rintro ⟨⟨i,j⟩,h⟩
  simp only [ι_comp_sigmaComparison_assoc]
  change integerCoefficientModuleFunctor.map
      (ιMapBifunctor K L integerTensorBifunctor (.down ℕ) i j n h) ≫
      integerCoefficientModuleFunctor.map ((chainIntegerTensorMap f g).f n) ≫ _ =
    integerCoefficientModuleFunctor.map
      (ιMapBifunctor K L integerTensorBifunctor (.down ℕ) i j n h) ≫ _
  rw [← CategoryTheory.Functor.map_comp_assoc, ι_chainIntegerTensorMap,
    CategoryTheory.Functor.map_comp, Category.assoc, map_ι_integerCoefficientTensorXIso,
    map_ι_integerCoefficientTensorXIso_assoc]
  rw [integerCoefficientTensorInv_naturality_assoc]
  congr 1
  symm
  change ιTensorObj _ _ i j n h ≫ (mapBifunctorMap _ _ _ _).f n = _
  rw [ι_mapBifunctorMap]
  change (_ ▷ _) ≫ (_ ◁ _) ≫ _ = _
  rw [← Category.assoc, ← MonoidalCategory.tensorHom_def]
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

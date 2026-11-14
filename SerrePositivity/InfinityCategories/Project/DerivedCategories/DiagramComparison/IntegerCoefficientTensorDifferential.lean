module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.IntegerCoefficientTensorDegrees
public import SerrePositivity.HomologicalAlgebra.NegativeTensorBaseChange

/-!
概要：整数係数テンソルの全次数比較と全複体の微分を照合する。
方針：各二重次数の包含で検出し、二つの部分微分と係数テンソルの自然性を使う。
規約：零次数と Koszul 符号を保ち、任意の宇宙の整数加群を扱う。
使われ方：HA 1.2.4、G10 の指定 EZ 比較の係数移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomologicalComplex
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (K L : ChainComplex (ModuleCat.{u} ℤ) ℕ)

/-- 次数が一致しない場合も含む包含の比較。 -/
@[reassoc]
theorem map_ιOrZero_integerCoefficientTensorXIso (i j n : ℕ) :
    integerCoefficientModuleFunctor.map
      (ιMapBifunctorOrZero K L integerTensorBifunctor (.down ℕ) i j n) ≫
      (integerCoefficientTensorXIso K L n).hom =
    (integerCoefficientTensorIso (K.X i) (L.X j)).inv ≫
      ιMapBifunctorOrZero
        ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj K)
        ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj L)
        (curriedTensor (ModuleCat simplicialRingCoefficient)) (.down ℕ) i j n := by
  by_cases h : i + j = n
  · rw [ιMapBifunctorOrZero_eq _ _ _ _ i j n h,
      ιMapBifunctorOrZero_eq _ _ _ _ i j n h]
    exact map_ι_integerCoefficientTensorXIso K L i j n h
  · rw [ιMapBifunctorOrZero_eq_zero _ _ _ _ i j n h,
      ιMapBifunctorOrZero_eq_zero _ _ _ _ i j n h]
    simp

/-- 第一の部分微分は指定全次数比較と可換。 -/
theorem map_d₁_integerCoefficientTensorXIso (i j n : ℕ) :
    integerCoefficientModuleFunctor.map
      (mapBifunctor.d₁ K L integerTensorBifunctor (.down ℕ) i j n) ≫
      (integerCoefficientTensorXIso K L n).hom =
    (integerCoefficientTensorIso (K.X i) (L.X j)).inv ≫
      mapBifunctor.d₁
        ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj K)
        ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj L)
        (curriedTensor (ModuleCat simplicialRingCoefficient)) (.down ℕ) i j n := by
  cases i with
  | zero =>
    rw [mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp),
      mapBifunctor.d₁_eq_zero _ _ _ _ _ _ _ (by simp)]
    simp
  | succ i =>
    rw [mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.down ℕ).Rel (i+1) i from rfl),
      mapBifunctor.d₁_eq' _ _ _ _ (show (ComplexShape.down ℕ).Rel (i+1) i from rfl)]
    simp only [Functor.map_units_smul, Functor.map_comp, Linear.units_smul_comp,
      Linear.comp_units_smul, Category.assoc]
    congr 1
    change integerCoefficientModuleFunctor.map (integerTensorMap (K.d (i+1) i) (𝟙 _)) ≫ _ ≫ _ =
      _ ≫ (integerCoefficientModuleFunctor.map (K.d (i+1) i) ▷ _) ≫ _
    rw [map_ιOrZero_integerCoefficientTensorXIso]
    rw [integerCoefficientTensorInv_naturality_assoc]
    simp

/-- 第二の部分微分も Koszul 符号を保って可換。 -/
theorem map_d₂_integerCoefficientTensorXIso (i j n : ℕ) :
    integerCoefficientModuleFunctor.map
      (mapBifunctor.d₂ K L integerTensorBifunctor (.down ℕ) i j n) ≫
      (integerCoefficientTensorXIso K L n).hom =
    (integerCoefficientTensorIso (K.X i) (L.X j)).inv ≫
      mapBifunctor.d₂
        ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj K)
        ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj L)
        (curriedTensor (ModuleCat simplicialRingCoefficient)) (.down ℕ) i j n := by
  cases j with
  | zero =>
    rw [mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp),
      mapBifunctor.d₂_eq_zero _ _ _ _ _ _ _ (by simp)]
    simp
  | succ j =>
    rw [mapBifunctor.d₂_eq' _ _ _ _ i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl),
      mapBifunctor.d₂_eq' _ _ _ _ i (show (ComplexShape.down ℕ).Rel (j+1) j from rfl)]
    simp only [Functor.map_units_smul, Functor.map_comp, Linear.units_smul_comp,
      Linear.comp_units_smul, Category.assoc]
    congr 1
    change integerCoefficientModuleFunctor.map (integerTensorMap (𝟙 _) (L.d (j+1) j)) ≫ _ ≫ _ =
      _ ≫ (_ ◁ integerCoefficientModuleFunctor.map (L.d (j+1) j)) ≫ _
    rw [map_ιOrZero_integerCoefficientTensorXIso]
    rw [integerCoefficientTensorInv_naturality_assoc]
    simp

/-- 指定された全次数比較は全微分と可換。 -/
theorem integerCoefficientTensorXIso_comm (n m : ℕ) :
    (integerCoefficientTensorXIso K L n).hom ≫
        (HomologicalComplex.tensorObj
          ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj K)
          ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj L)).d n m =
      integerCoefficientModuleFunctor.map ((chainIntegerTensor K L).d n m) ≫
        (integerCoefficientTensorXIso K L m).hom := by
  apply (cancel_epi (sigmaComparison integerCoefficientModuleFunctor
    (integerTensorSummand K L n))).1
  apply Sigma.hom_ext
  rintro ⟨⟨i,j⟩,h⟩
  simp only [ι_comp_sigmaComparison_assoc]
  change integerCoefficientModuleFunctor.map
      (ιMapBifunctor K L integerTensorBifunctor (.down ℕ) i j n h) ≫ _ ≫ _ =
    integerCoefficientModuleFunctor.map
      (ιMapBifunctor K L integerTensorBifunctor (.down ℕ) i j n h) ≫ _ ≫ _
  rw [map_ι_integerCoefficientTensorXIso_assoc, ← Functor.map_comp_assoc]
  simp only [mapBifunctor.d_eq, Preadditive.comp_add, mapBifunctor.ι_D₁,
    mapBifunctor.ι_D₂, Functor.map_add, Preadditive.add_comp]
  rw [map_d₁_integerCoefficientTensorXIso, map_d₂_integerCoefficientTensorXIso]

/-- 元の整数鎖テンソルの係数移送は、移した二因子の鎖テンソルと同型。 -/
def integerCoefficientChainTensorIso :
    (integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj
      (chainIntegerTensor K L) ≅
    HomologicalComplex.tensorObj
      ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj K)
      ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj L) :=
  HomologicalComplex.Hom.isoOfComponents (integerCoefficientTensorXIso K L)
    (fun n m _ => integerCoefficientTensorXIso_comm K L n m)

/-- 鎖複体の同型は元の二つの鎖写像に自然。 -/
theorem integerCoefficientChainTensorIso_naturality
    {K K' L L' : ChainComplex (ModuleCat.{u} ℤ) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    (integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).map
        (chainIntegerTensorMap f g) ≫ (integerCoefficientChainTensorIso K' L').hom =
      (integerCoefficientChainTensorIso K L).hom ≫ HomologicalComplex.tensorHom
        ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).map f)
        ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).map g) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact integerCoefficientTensorXIso_naturality f g n

/-- 整数係数の明示的テンソルを、同宇宙への移送と底変換の後に負次数テンソルへ結ぶ。 -/
def integerNegativeTensorBaseChangeIso {A : Type u} [CommRing A]
    (φ : simplicialRingCoefficient.{u} →+* A) :
    (((integerCoefficientModuleFunctor ⋙ ModuleCat.extendScalars φ).mapHomologicalComplex
      (.down ℕ)).obj (chainIntegerTensor K L)).extend ComplexShape.embeddingDownNat ≅
    HomologicalComplex.tensorObj
      ((((integerCoefficientModuleFunctor ⋙ ModuleCat.extendScalars φ).mapHomologicalComplex
        (.down ℕ)).obj K).extend ComplexShape.embeddingDownNat)
      ((((integerCoefficientModuleFunctor ⋙ ModuleCat.extendScalars φ).mapHomologicalComplex
        (.down ℕ)).obj L).extend ComplexShape.embeddingDownNat) :=
  (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat A)).mapIso
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (.down ℕ)).mapIso
      (integerCoefficientChainTensorIso K L)) ≪≫
    SerrePositivity.HomologicalAlgebra.negativeTensorBaseChangeIso φ
      ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj K)
      ((integerCoefficientModuleFunctor.mapHomologicalComplex (.down ℕ)).obj L)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

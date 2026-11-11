module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedSpace

/-!
# 自由整数単体的加群のテンソル比較

概要：集合の積の自由化と自由整数加群のテンソルを同定する。
方針：有限台関数のテンソル同型を各単体次数で使う。
規約：KST Definition A.3、Construction A.6。非被約であり、基底の augmentation は保持する。
使われ方：C(H) と ℤΔ¹ のテンソルによるホモトピーの界面。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 10
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory MonoidalCategory

/-- 概要：整数加群のテンソルを明示的に束ねる。
方針：通常の TensorProduct ℤ を使う。
規約：加群の宇宙は整数環の宇宙から独立。使われ方：KST Definition A.3 のテンソル。 -/
abbrev integerTensor (M N : ModuleCat.{u} ℤ) : ModuleCat.{u} ℤ :=
  ModuleCat.of ℤ (TensorProduct ℤ M N)

/-- 概要：整数加群の射のテンソル。
方針：通常のテンソル写像。
規約：KST Definition A.3。使われ方：単体的テンソルの遷移。 -/
abbrev integerTensorMap {M M' N N' : ModuleCat.{u} ℤ} (f : M ⟶ M') (g : N ⟶ N') :
    integerTensor M N ⟶ integerTensor M' N' :=
  ModuleCat.ofHom (TensorProduct.map f.hom g.hom)

/-- 概要：自由化の積とテンソルの標準同型。
方針：有限台関数のテンソル同型。
規約：KST Definition A.3 の ℤ(X×Y)=ℤX⊗ℤY。
使われ方：A.6 の幾何的な区間を加群のテンソル区間へ移す。 -/
def integerTensorIso (X Y : Type u) :
    integerTensor (integerLinearization.obj X) (integerLinearization.obj Y) ≅
      integerLinearization.obj (X × Y) :=
  (finsuppTensorFinsupp' ℤ X Y).toModuleIso

/-- 概要：テンソル比較は基底の純テンソルを対の基底へ送る。
方針：有限台関数の単項計算。
規約：KST Appendix A。使われ方：自然性と区間の両端条件。 -/
@[simp] lemma integerTensorIso_generator (X Y : Type u) (x : X) (y : Y) :
    (integerTensorIso X Y).hom
      (TensorProduct.tmul ℤ (integerGenerator x) (integerGenerator y)) =
        integerGenerator (x, y) := by
  change finsuppTensorFinsupp' ℤ X Y
    (TensorProduct.tmul ℤ (Finsupp.single x 1) (Finsupp.single y 1)) = _
  rw [finsuppTensorFinsupp'_single_tmul_single, mul_one]

/-- 概要：自由整数加群のテンソルからの射は二つの基底上で決まる。
方針：有限台関数のテンソル同型の逆を合成し、対の基底上で確認する。
規約：KST Appendix A。使われ方：自由化とテンソルの比較の自然性。 -/
lemma integerTensor_hom_ext {X Y : Type u} {M : ModuleCat.{u} ℤ}
    {f g : integerTensor (integerLinearization.obj X) (integerLinearization.obj Y) ⟶ M}
    (h : ∀ x y, f (TensorProduct.tmul ℤ (integerGenerator x) (integerGenerator y)) =
      g (TensorProduct.tmul ℤ (integerGenerator x) (integerGenerator y))) : f = g := by
  apply (cancel_epi (integerTensorIso X Y).inv).mp
  apply integerLinearization_hom_ext
  rintro ⟨x, y⟩
  change f ((finsuppTensorFinsupp' ℤ X Y).symm (Finsupp.single (x, y) 1)) =
    g ((finsuppTensorFinsupp' ℤ X Y).symm (Finsupp.single (x, y) 1))
  rw [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]
  exact h x y

/-- 概要：自由化のテンソル比較の自然性。
方針：二つの基底上で計算する。
規約：KST Appendix A。使われ方：次数ごとの同型を単体的な射へ組み立てる。 -/
lemma integerTensorIso_naturality {X X' Y Y' : Type u} (f : X ⟶ X') (g : Y ⟶ Y') :
    integerTensorMap (integerLinearization.map f) (integerLinearization.map g) ≫
      (integerTensorIso X' Y').hom =
    (integerTensorIso X Y).hom ≫ integerLinearization.map (↾fun p ↦ (f p.1, g p.2)) := by
  apply integerTensor_hom_ext
  intro x y
  change (integerTensorIso X' Y').hom
      (TensorProduct.tmul ℤ (integerLinearization.map f (integerGenerator x))
        (integerLinearization.map g (integerGenerator y))) =
    integerLinearization.map (↾fun p ↦ (f p.1, g p.2))
      ((integerTensorIso X Y).hom
        (TensorProduct.tmul ℤ (integerGenerator x) (integerGenerator y)))
  rw [integerLinearization_map_generator, integerLinearization_map_generator]
  rw [integerTensorIso_generator X Y x y]
  rw [integerLinearization_map_generator]
  exact integerTensorIso_generator X' Y' (f x) (g y)

/-- 概要：単体的整数加群の次数ごとのテンソル。
方針：テンソル写像で全ての単体射を送る。
規約：KST Definition A.3。使われ方：C⊗ℤΔ¹ の定義。 -/
def simplicialIntegerTensor (C D : SimplicialObject (ModuleCat.{u} ℤ)) :
    SimplicialObject (ModuleCat.{u} ℤ) where
  obj n := integerTensor (C.obj n) (D.obj n)
  map f := integerTensorMap (C.map f) (D.map f)
  map_id n := by
    apply ModuleCat.hom_ext
    simp [integerTensorMap]
  map_comp f g := by
    apply ModuleCat.hom_ext
    simp [integerTensorMap, TensorProduct.map_comp]

/-- 概要：二つの単体的整数加群射のテンソル。
方針：次数ごとのテンソル写像とその合成則を使う。
規約：KST Definition A.3。使われ方：区間ホモトピーの自然性。 -/
def simplicialIntegerTensorMap
    {C C' D D' : SimplicialObject (ModuleCat.{u} ℤ)} (f : C ⟶ C') (g : D ⟶ D') :
    simplicialIntegerTensor C D ⟶ simplicialIntegerTensor C' D' where
  app n := integerTensorMap (f.app n) (g.app n)
  naturality n m φ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    refine TensorProduct.inductionOn z (fun x y ↦ ?_) (fun x y hx hy ↦ ?_)
    · change TensorProduct.tmul ℤ (f.app m (C.map φ x)) (g.app m (D.map φ y)) =
        TensorProduct.tmul ℤ (C'.map φ (f.app n x)) (D'.map φ (g.app n y))
      exact congrArg₂ (TensorProduct.tmul ℤ)
        (congrArg (fun a ↦ a.hom x) (f.naturality φ))
        (congrArg (fun a ↦ a.hom y) (g.naturality φ))
    · simp only [map_add, hx, hy]

/-- 概要：単体的集合の積の自由化とテンソルとの比較。
方針：各次数の有限台関数の同型の自然性を用いる。
規約：KST Definition A.3。使われ方：A.6 の区間ホモトピーの自由化。 -/
def linearizedTensorComparison (X Y : SSet.{u}) :
    simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y) ⟶
      linearizedSpace (X ⊗ Y) where
  app n := (integerTensorIso (X.obj n) (Y.obj n)).hom
  naturality _n _m f := integerTensorIso_naturality (X.map f) (Y.map f)

/-- 概要：自由化と単体的テンソルとの標準同型。
方針：各次数の有限台関数の同型を自然性に沿って組み立てる。
規約：KST Definition A.3 の非被約なテンソル。
使われ方：幾何的な区間の自由化と C⊗ℤΔ¹ の同定。 -/
def linearizedTensorIso (X Y : SSet.{u}) :
    simplicialIntegerTensor (linearizedSpace X) (linearizedSpace Y) ≅
      linearizedSpace (X ⊗ Y) :=
  NatIso.ofComponents (fun n ↦ integerTensorIso (X.obj n) (Y.obj n))
    (fun f ↦ integerTensorIso_naturality (X.map f) (Y.map f))

/-- 概要：積の自由化との単体的テンソル同型は二つの写像に自然。
方針：次数ごとの有限台関数のテンソル比較の自然性を使う。
規約：KST Appendix A。使われ方：A.6 の実区間写像の自然性の移送。 -/
theorem linearizedTensorIso_naturality {X X' Y Y' : SSet.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    simplicialIntegerTensorMap (linearizedSpaceMap f) (linearizedSpaceMap g) ≫
        (linearizedTensorIso X' Y').hom =
      (linearizedTensorIso X Y).hom ≫ linearizedSpaceMap (f ⊗ₘ g) := by
  apply NatTrans.ext
  funext n
  exact integerTensorIso_naturality (f.app n) (g.app n)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

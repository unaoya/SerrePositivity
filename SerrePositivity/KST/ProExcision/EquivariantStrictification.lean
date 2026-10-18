module
public import SerrePositivity.KST.ProExcision.HomotopyStrictification
public import SerrePositivity.KST.ProExcision.LinearizedBarCylinder
public import SerrePositivity.KST.ProExcision.LinearizedEndpoints

/-!
# 同変な厳密化と augmentation 補正の相殺

概要：線形な区間ホモトピーの厳密化と相殺は外部 G の作用と可換する。
方針：端点と射影の同変性を基底で確認し、射の加減法と合成へ移す。
規約：KST Construction A.5 の右辺の augmentation 補正。非可換標的には
正本 §13-14 の μ:P×Q→H と因子内の入力ホモトピーを使う。
使われ方：因子内での同変な厳密化と Lemma 4.16 の同変な相殺。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial
variable {G : SimplicialObject MonCat.{u}} {X Y : SSet.{u}}
variable (A : SimplicialSetAction G X) (B : SimplicialSetAction G Y)

/-- 概要：単体的整数加群の射の外部 G に関する同変性。
方針：各次数の線形化した作用との可換性を指定する。
規約：KST Definition A.3。使われ方：加減法を含む A.5 の射の条件。 -/
def LinearizedEquivariant (f : linearizedSpace X ⟶ linearizedSpace Y) : Prop :=
  ∀ n a, linearizedSetAction A n a ≫ f.app n = f.app n ≫ linearizedSetAction B n a

/-- 概要：テンソル区間写像の外部 G 同変性。
方針：区間因子には恒等作用を与える。
規約：KST Definition A.3。使われ方：厳密化した全次数ホモトピーの同変性。 -/
def LinearizedCylinderEquivariant (h : linearizedCylinder X ⟶ linearizedSpace Y) : Prop :=
  ∀ n a, integerTensorMap (linearizedSetAction A n a) (𝟙 _) ≫ h.app n =
    h.app n ≫ linearizedSetAction B n a

/-- 概要：零端点は G 同変。
方針：自由加群の基底を零頂点との純テンソルへ送る。
規約：KST Construction A.5。使われ方：入力の区間写像の実始点の同変性。 -/
lemma linearizedEndpoint₀_equivariant (n : SimplexCategoryᵒᵖ) (a : G.obj n) :
    linearizedSetAction A n a ≫ (linearizedEndpoint₀ X).app n =
      (linearizedEndpoint₀ X).app n ≫ integerTensorMap (linearizedSetAction A n a) (𝟙 _) := by
  apply integerLinearization_hom_ext
  intro x
  change (linearizedEndpoint₀ X).app n
      (integerLinearization.map (↾(A.action n a)) (integerGenerator x)) = _
  rw [integerLinearization_map_generator, linearizedEndpoint₀_generator]
  change _ = integerTensorMap (linearizedSetAction A n a) (𝟙 _)
    ((linearizedEndpoint₀ X).app n (integerGenerator x))
  rw [linearizedEndpoint₀_generator]
  change _ = TensorProduct.tmul ℤ
    (integerLinearization.map (↾(A.action n a)) (integerGenerator x)) _
  rw [integerLinearization_map_generator]
  rfl

/-- 概要：一端点は G 同変。
方針：自由加群の基底を一頂点との純テンソルへ送る。
規約：KST Construction A.5。使われ方：入力の区間写像の実終点の同変性。 -/
lemma linearizedEndpoint₁_equivariant (n : SimplexCategoryᵒᵖ) (a : G.obj n) :
    linearizedSetAction A n a ≫ (linearizedEndpoint₁ X).app n =
      (linearizedEndpoint₁ X).app n ≫ integerTensorMap (linearizedSetAction A n a) (𝟙 _) := by
  apply integerLinearization_hom_ext
  intro x
  change (linearizedEndpoint₁ X).app n
      (integerLinearization.map (↾(A.action n a)) (integerGenerator x)) = _
  rw [integerLinearization_map_generator, linearizedEndpoint₁_generator]
  change _ = integerTensorMap (linearizedSetAction A n a) (𝟙 _)
    ((linearizedEndpoint₁ X).app n (integerGenerator x))
  rw [linearizedEndpoint₁_generator]
  change _ = TensorProduct.tmul ℤ
    (integerLinearization.map (↾(A.action n a)) (integerGenerator x)) _
  rw [integerLinearization_map_generator]
  rfl

/-- 概要：テンソル区間の射影は G 同変。
方針：純テンソルの基底で幾何的な第一射影を評価する。
規約：KST Construction A.5。使われ方：同変な定数区間写像。 -/
lemma linearizedCylinderProjection_equivariant :
    LinearizedCylinderEquivariant A A (linearizedCylinderProjection X) := by
  intro n a
  apply integerTensor_hom_ext (X := X.obj n) (Y := (Δ[1] : SSet.{u}).obj n)
  intro x t
  change (linearizedCylinderProjection X).app n
    (TensorProduct.tmul ℤ
      (integerLinearization.map (↾(A.action n a)) (integerGenerator x)) (integerGenerator t)) = _
  rw [integerLinearization_map_generator]
  change integerLinearization.map ((CartesianMonoidalCategory.fst X Δ[1]).app n)
      ((integerTensorIso (X.obj n) ((Δ[1] : SSet.{u}).obj n)).hom
        (TensorProduct.tmul ℤ (integerGenerator (A.action n a x)) (integerGenerator t))) = _
  rw [integerTensorIso_generator, integerLinearization_map_generator]
  change _ = integerLinearization.map (↾(A.action n a))
    (integerLinearization.map ((CartesianMonoidalCategory.fst X Δ[1]).app n)
      ((integerTensorIso (X.obj n) ((Δ[1] : SSet.{u}).obj n)).hom
        (TensorProduct.tmul ℤ (integerGenerator x) (integerGenerator t))))
  rw [integerTensorIso_generator, integerLinearization_map_generator,
    integerLinearization_map_generator]
  rfl

variable {A B}

/-- 概要：同変な射の和は同変。
方針：合成の加法性を使う。規約：KST A.5 の非被約模型。
使われ方：augmentation 補正の同変性。 -/
lemma LinearizedEquivariant.add {f g : linearizedSpace X ⟶ linearizedSpace Y}
    (hf : LinearizedEquivariant A B f) (hg : LinearizedEquivariant A B g) :
    LinearizedEquivariant A B (f + g) := by
  intro n a
  simp only [NatTrans.app_add, Preadditive.comp_add, Preadditive.add_comp, hf n a, hg n a]

/-- 概要：同変な射の差は同変。
方針：合成の加法性を使う。規約：KST A.5 の右辺の augmentation 補正。
使われ方：厳密化した射の同変性。 -/
lemma LinearizedEquivariant.sub {f g : linearizedSpace X ⟶ linearizedSpace Y}
    (hf : LinearizedEquivariant A B f) (hg : LinearizedEquivariant A B g) :
    LinearizedEquivariant A B (f - g) := by
  intro n a
  simp only [NatTrans.app_sub, Preadditive.comp_sub, Preadditive.sub_comp, hf n a, hg n a]

/-- 概要：同変区間写像の実始点は同変。
方針：零端点の同変性と区間写像の同変性を合成する。
規約：KST A.5、全次数。使われ方：低次厳密化の始点補正。 -/
lemma LinearizedCylinderEquivariant.endpoint₀
    {h : linearizedCylinder X ⟶ linearizedSpace Y}
    (hh : LinearizedCylinderEquivariant A B h) :
    LinearizedEquivariant A B (linearizedEndpoint₀ X ≫ h) := by
  intro n a
  change _ ≫ ((linearizedEndpoint₀ X).app n ≫ h.app n) = _
  rw [← Category.assoc, linearizedEndpoint₀_equivariant A n a, Category.assoc, hh n a]
  simp only [Category.assoc, NatTrans.comp_app]

/-- 概要：同変区間写像の実終点は同変。
方針：一端点と区間写像の同変性を合成する。
規約：KST A.5、全次数。使われ方：低次厳密化の終点補正。 -/
lemma LinearizedCylinderEquivariant.endpoint₁
    {h : linearizedCylinder X ⟶ linearizedSpace Y}
    (hh : LinearizedCylinderEquivariant A B h) :
    LinearizedEquivariant A B (linearizedEndpoint₁ X ≫ h) := by
  intro n a
  change _ ≫ ((linearizedEndpoint₁ X).app n ≫ h.app n) = _
  rw [← Category.assoc, linearizedEndpoint₁_equivariant A n a, Category.assoc, hh n a]
  simp only [Category.assoc, NatTrans.comp_app]

/-- 概要：同変な定数射から作る区間写像は同変。
方針：射影と定数射の同変性を合成する。
規約：KST A.5。使われ方：厳密化ホモトピーと相殺の定数部分。 -/
lemma LinearizedEquivariant.constant
    {f : linearizedSpace X ⟶ linearizedSpace Y} (hf : LinearizedEquivariant A B f) :
    LinearizedCylinderEquivariant A B (linearizedCylinderProjection X ≫ f) := by
  intro n a
  change _ ≫ ((linearizedCylinderProjection X).app n ≫ f.app n) = _
  rw [← Category.assoc, linearizedCylinderProjection_equivariant A n a,
    Category.assoc, hf n a]
  simp only [Category.assoc, NatTrans.comp_app]

/-- 概要：同変な区間写像の和は同変。
方針：合成の加法性を使う。規約：KST A.5。
使われ方：厳密化したホモトピーの同変性。 -/
lemma LinearizedCylinderEquivariant.add
    {h k : linearizedCylinder X ⟶ linearizedSpace Y}
    (hh : LinearizedCylinderEquivariant A B h) (hk : LinearizedCylinderEquivariant A B k) :
    LinearizedCylinderEquivariant A B (h + k) := by
  intro n a
  simp only [NatTrans.app_add, Preadditive.comp_add, Preadditive.add_comp, hh n a, hk n a]

/-- 概要：同変な区間写像の差は同変。
方針：合成の加法性を使う。規約：KST A.5 の右辺の augmentation 補正。
使われ方：Lemma 4.16 の相殺の同変性。 -/
lemma LinearizedCylinderEquivariant.sub
    {h k : linearizedCylinder X ⟶ linearizedSpace Y}
    (hh : LinearizedCylinderEquivariant A B h) (hk : LinearizedCylinderEquivariant A B k) :
    LinearizedCylinderEquivariant A B (h - k) := by
  intro n a
  simp only [NatTrans.app_sub, Preadditive.comp_sub, Preadditive.sub_comp, hh n a, hk n a]

/-- 概要：低次厳密化は外部 G 同変な射を保つ。
方針：入力射と二つの実端点の加減法に帰着する。
規約：KST A.5、因子内での厳密化。使われ方：C(P)、C(Q) の厳密化。 -/
lemma LinearizedMHomotopy.strictifiedMap_equivariant
    {f g : linearizedSpace X ⟶ linearizedSpace Y} {m : ℕ}
    (H : LinearizedMHomotopy f g m) (hf : LinearizedEquivariant A B f)
    (hh : LinearizedCylinderEquivariant A B H.h) :
    LinearizedEquivariant A B H.strictifiedMap :=
  (hf.sub hh.endpoint₀).add hh.endpoint₁

/-- 概要：厳密化への全次数ホモトピーも外部 G 同変。
方針：同変な定数区間写像に入力の区間写像を加える。
規約：KST A.5、因子内の入力を用いる。使われ方：μ を適用する前の同変な比較。 -/
lemma LinearizedMHomotopy.strictificationHomotopy_equivariant
    {f g : linearizedSpace X ⟶ linearizedSpace Y} {m : ℕ}
    (H : LinearizedMHomotopy f g m) (hf : LinearizedEquivariant A B f)
    (hh : LinearizedCylinderEquivariant A B H.h) :
    LinearizedCylinderEquivariant A B H.strictificationHomotopy.h :=
  (hf.sub hh.endpoint₀).constant.add hh

/-- 概要：augmentation 補正の相殺で得るホモトピーは外部 G 同変。
方針：同変な定数区間写像と入力区間写像の差を取る。
規約：KST Lemma 4.16、C(ψ)≃C(ψ)+C(φ)−C(e) から C(φ)≃C(e)。
使われ方：非可換なブロック行列群への A.5 の適用。 -/
lemma LinearizedMHomotopy.cancel_augmentation_equivariant
    {ψ φ e : linearizedSpace X ⟶ linearizedSpace Y} {m : ℕ}
    (H : LinearizedMHomotopy ψ (ψ + φ - e) m)
    (hψ : LinearizedEquivariant A B ψ) (hφ : LinearizedEquivariant A B φ)
    (hh : LinearizedCylinderEquivariant A B H.h) :
    LinearizedCylinderEquivariant A B H.cancel_augmentation.h :=
  (hψ.add hφ).constant.sub hh

end SerrePositivity.KST.ProExcision


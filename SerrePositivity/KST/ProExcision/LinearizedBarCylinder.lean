module
public import SerrePositivity.KST.ProExcision.LinearizedActionBarFibers
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.IntegerLinearizationDesc
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedHomotopy

/-!
# 同変な線形区間写像の作用 bar への持ち上げ

概要：G 同変な C(X)⊗ℤΔ¹→C(Y) を C(E_X G)⊗ℤΔ¹→C(E_Y G) へ送る。
方針：始点に入力の線形区間写像を適用し、G の語を固定した係数の包含へ送る。
規約：KST Definition A.3、Lemma A.4。区間写像を基底を保つ写像と仮定しない。
使われ方：m 次ホモトピーを半直積のホモロジーへ移すための線形構成。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open SerrePositivity.KST.Comparison
open scoped Simplicial
variable {G : SimplicialObject MonCat.{u}} {X Y : SSet.{u}}
variable {A : SimplicialSetAction G X} {B : SimplicialSetAction G Y}

/-- 概要：G 同変な非被約自由整数加群の区間写像。
方針：単体的区間写像と、各 G 元の作用との可換条件を保持する。
規約：KST Definition A.3 の両端条件を付ける前の数学的データ。
使われ方：Lemma A.4 の m 次ホモトピーの区間部分。 -/
structure EquivariantLinearizedCylinderMap (A : SimplicialSetAction G X)
    (B : SimplicialSetAction G Y) where
  h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace Y
  equivariant (n : SimplexCategoryᵒᵖ) (a : G.obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (linearizedSetAction A n a) (𝟙 _) ≫ h.app n =
      h.app n ≫ linearizedSetAction B n a

/-- 概要：同変区間写像の bar への持ち上げの各次数の成分。
方針：基底の始点に区間写像を適用し、元の G の語を固定して線形に入れる。
規約：KST Lemma A.4。非被約な全自由加群。
使われ方：単体的自然性と両端条件の検証。 -/
def linearizedActionBarCylinderApp (H : EquivariantLinearizedCylinderMap A B)
    (n : SimplexCategoryᵒᵖ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder (setActionBar A)).obj n ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (setActionBar B)).obj n :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso ((setActionBar A).obj n) ((Δ[1] : SSet.{u}).obj n)).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun z ↦
      linearizedActionBarFiber B n ((setActionBarProjection A).app n z.1)
        (H.h.app n (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (z.1.obj 0).val)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator z.2))))

/-- 概要：bar の区間写像の各次数の基底上の公式。
方針：テンソルの基底同型と整数線形拡張を評価する。
規約：KST Lemma A.4。使われ方：自然性と m 次両端の比較。 -/
@[simp] lemma linearizedActionBarCylinderApp_generator
    (H : EquivariantLinearizedCylinderMap A B) (n : SimplexCategoryᵒᵖ)
    (p : (setActionBar A).obj n) (t : (Δ[1] : SSet.{u}).obj n) :
    linearizedActionBarCylinderApp H n
      (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator t)) =
        linearizedActionBarFiber B n ((setActionBarProjection A).app n p)
          (H.h.app n (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (p.obj 0).val)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator t))) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun z ↦
      linearizedActionBarFiber B n ((setActionBarProjection A).app n z.1)
        (H.h.app n (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (z.1.obj 0).val)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator z.2))))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso ((setActionBar A).obj n) ((Δ[1] : SSet.{u}).obj n)).hom
      (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator t))) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorIso_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator]

/-- 概要：同変な線形区間写像は作用 bar の単体的区間写像へ持ち上がる。
方針：語の射影の自然性、始点の prefix の変化、入力の同変性と単体的自然性を合成する。
規約：KST Lemma A.4。bar への持ち上げの存在を仮定しない。
使われ方：m 次ホモトピーの作用 bar への移送。 -/
def linearizedActionBarCylinderMap (H : EquivariantLinearizedCylinderMap A B) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinder (setActionBar A) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (setActionBar B) where
  app n := linearizedActionBarCylinderApp H n
  naturality n m f := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensor_hom_ext (X := (setActionBar A).obj n) (Y := (Δ[1] : SSet.{u}).obj n)
    intro p t
    change linearizedActionBarCylinderApp H m
        (TensorProduct.tmul ℤ
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((setActionBar A).map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((Δ[1] : SSet.{u}).map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator t))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((setActionBar B).map f)
        (linearizedActionBarCylinderApp H n
          (TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator p) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator t)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator,
      linearizedActionBarCylinderApp_generator, linearizedActionBarCylinderApp_generator,
      setActionBar_map_projection, setActionBar_map_source]
    let w := (setActionBarProjection A).app n p
    let a := barWordFacePrefix f w
    let v := TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (p.obj 0).val) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator t)
    have he := congrArg (fun q ↦ q.hom (H.h.app n v))
      (linearizedActionBarFiber_naturality B f w)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((setActionBar B).map f)
        (linearizedActionBarFiber B n w (H.h.app n v)) =
      linearizedActionBarFiber B m ((monoidBar G).map f w)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (Y.map f) (linearizedSetAction B n a (H.h.app n v))) at he
    rw [he]
    apply congrArg (linearizedActionBarFiber B m ((monoidBar G).map f w))
    have hE := congrArg (fun q ↦ q.hom v) (H.equivariant n a)
    change H.h.app n (TensorProduct.tmul ℤ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (↾(A.action n a)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (p.obj 0).val))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator t)) = linearizedSetAction B n a (H.h.app n v) at hE
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator] at hE
    let v' := TensorProduct.tmul ℤ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (A.action n a (p.obj 0).val))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator t)
    have hN := congrArg (fun q ↦ q.hom v') (H.h.naturality f)
    change H.h.app m (TensorProduct.tmul ℤ
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (X.map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (A.action n a (p.obj 0).val)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((Δ[1] : SSet.{u}).map f) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator t))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (Y.map f) (H.h.app n v') at hN
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator] at hN
    exact hN.trans (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (Y.map f)) hE)

end SerrePositivity.KST.ProExcision

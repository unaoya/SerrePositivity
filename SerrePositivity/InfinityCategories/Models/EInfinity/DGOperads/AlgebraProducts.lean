module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraLimitCriterion
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod

/-!
模型。文献の定義との比較は後で
# オペラッド代数の積

概要：Berger–Moerdijk §1 の代数の二項積を底の複体の直和上に構成する。
方針：演算を二つの射影後に指定し、共同単射性で代数公理を検証する。
規約：積は arity 0 の作用も保ち、モデル構造は使わない。
使われ方：二端点評価を代数の積への射として束ねる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：底の直和に射影ごとの作用で二項積の代数構造を入れる（BM §1）。
方針：Bool で添字付けた二つの射影へ代数公理の判定を適用する。
規約：false は第一射影、true は第二射影。
使われ方：path object の二端点評価の値域となる。 -/
def binaryProduct (X Y : P.Algebra) : P.Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ofJointlyMonicActions (X.carrier ⊞ Y.carrier) (fun b : Bool => if b then Y else X)
    (fun b => by
      cases b
      · exact biprod.fst
      · exact biprod.snd)
    (fun n => biprod.lift
      ((P.arity n ◁ _root_.SerrePositivity.TensorPowers.map biprod.fst n) ≫ X.action n)
      ((P.arity n ◁ _root_.SerrePositivity.TensorPowers.map biprod.snd n) ≫ Y.action n))
    (by intro b n; cases b
        · exact biprod.lift_fst _ _
        · exact biprod.lift_snd _ _)
    (by
      intro T f g h
      apply biprod.hom_ext
      · exact h false
      · exact h true)

/-- 概要：代数の二項積の第一射影（BM §1）。
方針：作用の第一成分を評価する。
規約：底の射は複体の直和の第一射影。
使われ方：積の普遍性と二端点評価の比較に用いる。 -/
def binaryProductFst (X Y : P.Algebra) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProduct X Y ⟶ X where
  hom := biprod.fst
  comm n := by
    change biprod.lift _ _ ≫ biprod.fst = _
    rw [biprod.lift_fst, id_tensorHom]

/-- 概要：代数の二項積の第二射影（BM §1）。
方針：作用の第二成分を評価する。
規約：底の射は複体の直和の第二射影。
使われ方：積の普遍性と二端点評価の比較に用いる。 -/
def binaryProductSnd (X Y : P.Algebra) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProduct X Y ⟶ Y where
  hom := biprod.snd
  comm n := by
    change biprod.lift _ _ ≫ biprod.snd = _
    rw [biprod.lift_snd, id_tensorHom]

/-- 概要：二つの代数射を積への代数射に束ねる（BM §1）。
方針：底の直和への射を取り、二つの射影後に作用保存を検証する。
規約：底の射は biprod.lift と厳密に一致する。
使われ方：定数射と二端点評価の三角形を代数の圏で述べる。 -/
def binaryProductLift {Z X Y : P.Algebra} (f : Z ⟶ X) (g : Z ⟶ Y) :
    Z ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProduct X Y where
  hom := biprod.lift f.hom g.hom
  comm n := by
    change Z.action n ≫ biprod.lift f.hom g.hom =
      (𝟙 (P.arity n) ⊗ₘ _root_.SerrePositivity.TensorPowers.map (biprod.lift f.hom g.hom) n) ≫
        biprod.lift _ _
    simp only [id_tensorHom]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst]
      rw [f.comm, id_tensorHom, ← whiskerLeft_comp_assoc, ← _root_.SerrePositivity.TensorPowers.map_comp]
      rw [biprod.lift_fst]
    · simp only [Category.assoc, biprod.lift_snd]
      rw [g.comm, id_tensorHom, ← whiskerLeft_comp_assoc, ← _root_.SerrePositivity.TensorPowers.map_comp]
      rw [biprod.lift_snd]

/-- 概要：二つの射影は代数射を共同に判定する（BM §1）。
方針：忠実な忘却後に直和の射の外延性を適用する。
規約：積の代数射としての等式を判定する。
使われ方：積の極限性と path object の三角形を検証する。 -/
lemma binaryProduct_hom_ext {Z X Y : P.Algebra} (f g : Z ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProduct X Y)
    (h₁ : f ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductFst X Y = g ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductFst X Y)
    (h₂ : f ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductSnd X Y = g ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductSnd X Y) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
  apply biprod.hom_ext
  · exact congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.hom h₁
  · exact congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.hom h₂

/-- 概要：底の直和で作った代数の積錐（BM §1）。
方針：二つの代数射としての射影を錐に束ねる。
規約：底の頂点は複体の直和そのもの。
使われ方：忘却後の積との比較と積の存在を与える。 -/
def binaryProductCone (X Y : P.Algebra) : BinaryFan X Y :=
  BinaryFan.mk (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductFst X Y) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductSnd X Y)

/-- 概要：底の直和で作った錐は代数の圏で極限となる（BM §1）。
方針：二つの代数射の持ち上げと射影による外延性を使う。
規約：積の普遍性を代数射について証明する。
使われ方：二端点評価の値域が実際の代数の積であることを保証する。 -/
def binaryProductIsLimit (X Y : P.Algebra) : IsLimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductCone X Y) :=
  BinaryFan.isLimitMk (fun s => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductLift s.fst s.snd)
    (fun s => by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext; exact biprod.lift_fst _ _)
    (fun s => by apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext; exact biprod.lift_snd _ _)
    (fun s f h₁ h₂ => by
      apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProduct_hom_ext
      · exact h₁.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext (biprod.lift_fst _ _)).symm
      · exact h₂.trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext (biprod.lift_snd _ _)).symm)

/-- 概要：オペラッド代数は二項積を持つ（BM §1）。
方針：底の直和上に構成した極限錐を用いる。
規約：モデル構造を仮定しない。
使われ方：Mathlib の path object の積を選べるようにする。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.instHasBinaryProduct (X Y : P.Algebra) : HasBinaryProduct X Y :=
  ⟨⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductCone X Y, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIsLimit X Y⟩⟩

/-- 概要：選んだ圏論的積と底の直和上の積代数の標準比較（BM §1）。
方針：二つの極限錐の一意な同型を用いる。
規約：この同型を忘却して底の複体の積を比較する。
使われ方：Mathlib の path object の評価の fibration 性を移す。 -/
def binaryProductIso (X Y : P.Algebra) : X ⨯ Y ≅ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProduct X Y :=
  limit.isoLimitCone ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductCone X Y, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIsLimit X Y⟩

/-- 概要：積の比較は第一射影を保つ（BM §1）。
方針：極限錐の比較の射影公式を評価する。
規約：選んだ積から底の直和上の積への向き。
使われ方：二端点評価の標準比較を証明する。 -/
@[reassoc]
lemma binaryProductIso_hom_fst (X Y : P.Algebra) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIso X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductFst X Y = prod.fst :=
  limit.isoLimitCone_hom_π
    ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductCone X Y, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIsLimit X Y⟩ ⟨WalkingPair.left⟩

/-- 概要：積の比較は第二射影を保つ（BM §1）。
方針：極限錐の比較の射影公式を評価する。
規約：選んだ積から底の直和上の積への向き。
使われ方：二端点評価の標準比較を証明する。 -/
@[reassoc]
lemma binaryProductIso_hom_snd (X Y : P.Algebra) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIso X Y).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductSnd X Y = prod.snd :=
  limit.isoLimitCone_hom_π
    ⟨_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductCone X Y, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.binaryProductIsLimit X Y⟩ ⟨WalkingPair.right⟩

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

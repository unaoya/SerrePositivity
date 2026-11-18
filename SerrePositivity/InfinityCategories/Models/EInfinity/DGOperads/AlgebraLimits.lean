module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraLimitCriterion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraIso
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Creates

/-!
模型。文献の定義との比較は後で
# 底の複体で作るオペラッド代数の極限

概要：Berger–Moerdijk §1 の代数の忘却関手が極限を作ることを示す。
方針：極限錐の各射影の後で作用を定義し、共同単射性で公理を検証する。
規約：空の図式を含む任意の形の底の極限を持ち上げる。
使われ方：転送定理に必要な有限極限と、忘却による極限の計算を供給する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：忘却関手は代数の同型を反映する（BM §1）。
方針：底の同型を作用を保つ代数の同型に持ち上げる。
規約：モデル構造を使わない。
使われ方：極限錐の持ち上げから極限の創出を導く。 -/
instance forget_reflectsIsomorphisms : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).ReflectsIsomorphisms where
  reflects f _ := by
    have : IsIso f.hom := inferInstanceAs (IsIso ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).map f))
    let e := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.isoOfCarrierIso (asIso f.hom) f.comm
    have he : e.hom = f := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext rfl
    rw [← he]
    infer_instance

variable {J : Type w} [Category.{v} J] (F : J ⥤ P.Algebra)
  (c : Cone (F ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P)) (hc : IsLimit c)

/-- 概要：底の極限上の各演算を定める錐（BM §1）。
方針：入力を各射影で移してから図式の代数の作用を適用する。
規約：演算の入力数は零を許す。
使われ方：極限の普遍性で極限上の作用を定義する。 -/
def limitActionCone (n : ℕ) : Cone (F ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) where
  pt := P.arity n ⊗ power c.pt n
  π.app j := (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (c.π.app j) n) ≫ (F.obj j).action n
  π.naturality i j f := by
    change 𝟙 _ ≫ _ =
      ((P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (c.π.app i) n) ≫ (F.obj i).action n) ≫ (F.map f).hom
    rw [Category.id_comp]
    symm
    rw [Category.assoc, (F.map f).comm, id_tensorHom,
      ← whiskerLeft_comp_assoc, ← _root_.SerrePositivity.TensorPowers.map_comp]
    exact congrArg (fun k => (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map k n) ≫ (F.obj j).action n)
      (c.w f)

/-- 概要：底の極限錐に誘導されるオペラッド代数（BM §1）。
方針：作用の錐の普遍射を取り、極限射影の共同単射性を使う。
規約：極限錐の頂点を厳密に保持する。
使われ方：極限錐を代数の圏へ持ち上げる。 -/
def ofLimitCone : P.Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ofJointlyMonicActions c.pt (fun j => F.obj j) (fun j => c.π.app j)
    (fun n => hc.lift (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.limitActionCone F c n))
    (fun j n => hc.fac (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.limitActionCone F c n) j)
    (fun _ _ h => hc.hom_ext h)

/-- 概要：底の極限錐の持ち上げは元の代数図式の錐（BM §1）。
方針：底の各射影の作用保存を作用の普遍射の公式から得る。
規約：忘却後の射影は元の錐の射影そのもの。
使われ方：極限の創出の持ち上げデータとなる。 -/
def algebraLimitCone : Cone F where
  pt := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ofLimitCone F c hc
  π.app j := {
    hom := c.π.app j
    comm n := by
      change hc.lift (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.limitActionCone F c n) ≫ c.π.app j = _
      rw [hc.fac, id_tensorHom]
      rfl }
  π.naturality i j f := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact c.π.naturality f

/-- 概要：底の極限への普遍射は代数射（BM §1）。
方針：作用保存を全ての極限射影の後で判定する。
規約：任意の代数の錐を入力に取る。
使われ方：持ち上げた錐の極限性を証明する。 -/
def algebraLimitLift (s : Cone F) : s.pt ⟶ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.algebraLimitCone F c hc).pt where
  hom := hc.lift ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCone s)
  comm n := by
    change s.pt.action n ≫ hc.lift ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCone s) =
      (𝟙 (P.arity n) ⊗ₘ _root_.SerrePositivity.TensorPowers.map (hc.lift ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCone s)) n) ≫
        hc.lift (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.limitActionCone F c n)
    rw [id_tensorHom]
    apply hc.hom_ext
    intro j
    simp only [Category.assoc, hc.fac]
    change s.pt.action n ≫ (s.π.app j).hom =
      (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (hc.lift ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCone s)) n) ≫
        (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (c.π.app j) n) ≫ (F.obj j).action n
    erw [(s.π.app j).comm, id_tensorHom, ← whiskerLeft_comp_assoc,
      ← _root_.SerrePositivity.TensorPowers.map_comp, hc.fac]
    rfl

/-- 概要：底の極限から持ち上げた代数の錐は極限（BM §1）。
方針：普遍射を代数射へ上げ、忘却の忠実性で射影公式と一意性を移す。
規約：元の極限の形や大きさを制限しない。
使われ方：忘却関手が極限を作ることを示す。 -/
def algebraLimitIsLimit : IsLimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.algebraLimitCone F c hc) where
  lift := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.algebraLimitLift F c hc
  fac s j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext (hc.fac ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCone s) j)
  uniq s m h := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    apply hc.uniq ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCone s)
    intro j
    exact congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.hom (h j)

/-- 概要：オペラッド代数の忘却関手は全ての底の極限を作る（BM §1）。
方針：任意の底の極限錐を頂点ごと持ち上げ、同型の反映を使う。
規約：底に極限が存在しない形にも存在を仮定せずに創出を述べる。
使われ方：複体の極限から代数の極限とその保存を得る。 -/
instance forget_createsLimit : CreatesLimit F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) :=
  createsLimitOfReflectsIso (fun c hc => {
    liftedCone := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.algebraLimitCone F c hc
    validLift := Iso.refl _
    makesLimit := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.algebraLimitIsLimit F c hc })

/-- 概要：忘却関手は任意の形の極限を作る（BM §1）。
方針：個々の図式についての創出を形ごとに束ねる。
規約：形の対象・射の宇宙は独立。
使われ方：存在する底の極限から代数の極限を得る。 -/
instance forget_createsLimitsOfShape : CreatesLimitsOfShape J (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) where
  CreatesLimit := inferInstance

/-- 概要：忘却関手の極限の創出を任意の宇宙の形に束ねる（BM §1）。
方針：形ごとの創出を宇宙サイズの構造へ登録する。
規約：形の対象・射の宇宙は独立。
使われ方：忘却の小極限保存を自動推論で使う。 -/
instance forget_createsLimitsOfSize : CreatesLimitsOfSize.{v, w} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) where
  CreatesLimitsOfShape := inferInstance

/-- 概要：底にある任意の形の極限は代数の圏にも存在する（BM §1）。
方針：忘却関手の極限の創出を適用する。
規約：底の形ごとの極限の存在だけを使う。
使われ方：複体から小極限と有限極限を得る。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.instHasLimitsOfShapeOfComplex [HasLimitsOfShape J (Complex A)] : HasLimitsOfShape J P.Algebra :=
  hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P)

/-- 概要：オペラッド代数は全ての小極限を持つ（BM §1）。
方針：複体の小極限を忘却関手に沿って作る。
規約：係数環の宇宙内の小さい図式を扱う。
使われ方：右転送定理の有限極限の入力を供給する。 -/
instance _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.instHasLimitsOfSize : HasLimitsOfSize.{u, u} P.Algebra where
  has_limits_of_shape := inferInstance

/-- 概要：忘却関手は全ての小極限を保つ（BM §1）。
方針：形ごとの創出と複体の極限から得た保存を宇宙サイズに束ねる。
規約：係数環の宇宙内の小さい図式を扱う。
使われ方：代数の極限を底の複体で計算する。 -/
instance forget_preservesLimitsOfSize : PreservesLimitsOfSize.{u, u} (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) where
  preservesLimitsOfShape := inferInstance

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

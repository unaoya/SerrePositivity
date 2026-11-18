module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraColimitCriterion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraLimits
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorPowerColimits

/-!
模型。文献の定義との比較は後で
# テンソル冪が保つ底の余極限の持ち上げ

概要：Berger–Moerdijk §1 の代数の忘却関手はテンソル冪が保つ底の余極限を作る。
方針：演算の余錐の普遍射で作用を定め、入力の共同全射性で公理を検証する。
規約：図式ごとの保存だけを要求し、モデル構造は使わない。
使われ方：sifted・filtered 余極限と reflexive coequalizer を代数に構成する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：固定係数と有限テンソル冪の演算の入力関手（BM §1）。
方針：有限テンソル冪の後で係数を左からテンソルする。
規約：零次の冪も含む。
使われ方：作用の降下とその共同全射な入力族を統一的に扱う。 -/
def operationInputFunctor (Q : Complex A) (n : ℕ) : Complex A ⥤ Complex A :=
  powerFunctor n ⋙ tensorLeft Q

variable {J : Type w} [Category.{v} J] (F : J ⥤ P.Algebra)
  (c : Cocone (F ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P)) (hc : IsColimit c)
  [∀ n, PreservesColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) (powerFunctor n)]

/-- 概要：係数付きの有限入力関手は指定した底の余極限を保つ（BM §1）。
方針：テンソル冪の保存と固定係数の閉モノイダル随伴を合成する。
規約：保存の入力は図式ごとの仮定だけ。
使われ方：作用と代数公理を底の余極限へ降ろす。 -/
instance operationInput_preservesColimit (Q : Complex A) (n : ℕ) :
    PreservesColimit (F ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.operationInputFunctor Q n) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.operationInputFunctor
  infer_instance

/-- 概要：底の余極限上の作用を定める余錐（BM §1）。
方針：各代数の作用の後で元の余極限の構造射を合成する。
規約：演算の係数は arity ごとに固定する。
使われ方：係数付き入力の余極限の普遍射で作用を得る。 -/
def colimitActionCocone (n : ℕ) :
    Cocone ((F ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.operationInputFunctor (P.arity n) n) where
  pt := c.pt
  ι.app j := (F.obj j).action n ≫ c.ι.app j
  ι.naturality i j f := by
    change (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (F.map f).hom n) ≫
      ((F.obj j).action n ≫ c.ι.app j) = ((F.obj i).action n ≫ c.ι.app i) ≫ 𝟙 _
    rw [Category.comp_id, ← id_tensorHom, ← reassoc_of% ((F.map f).comm n)]
    exact congrArg (fun k => (F.obj i).action n ≫ k) (c.w f)

/-- 概要：底の余極限へ降りる各 arity の作用（BM §1）。
方針：係数付き入力の余極限から作用の余錐への普遍射を取る。
規約：作用は実際の複体射。
使われ方：余極限の頂点を代数にする。 -/
def colimitAction (n : ℕ) : P.arity n ⊗ power c.pt n ⟶ c.pt :=
  (isColimitOfPreserves (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.operationInputFunctor (P.arity n) n) hc).desc
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.colimitActionCocone F c n)

/-- 概要：余極限の構造射は降りた作用を保つ（BM §1）。
方針：作用を定める普遍射の構造射との合成公式を使う。
規約：係数の恒等射は左 whisker で表す。
使われ方：共同全射な入力族による代数公理の判定に用いる。 -/
@[reassoc]
lemma colimitAction_ι (n : ℕ) (j : J) :
    (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (c.ι.app j) n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.colimitAction F c hc n =
      (F.obj j).action n ≫ c.ι.app j :=
  (isColimitOfPreserves (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.operationInputFunctor (P.arity n) n) hc).fac _ j

/-- 概要：底の余極限の頂点に代数構造を入れる（BM §1）。
方針：降りた作用と係数付き入力の余極限の共同全射性を使う。
規約：底の余極限の頂点を厳密に保持する。
使われ方：忘却関手の余極限の創出を構成する。 -/
def ofColimitCocone : P.Algebra :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ofJointlyEpicActions c.pt (fun j => F.obj j) (fun j => c.ι.app j)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.colimitAction F c hc) (fun j n => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.colimitAction_ι F c hc n j)
    (fun Q n {_} _ _ h =>
      (isColimitOfPreserves (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.operationInputFunctor Q n) hc).hom_ext h)

/-- 概要：底の余極限の構造射を代数射へ持ち上げる（BM §1）。
方針：作用の降下の構造射公式を使う。
規約：忘却後の余錐は元の余錐そのもの。
使われ方：余極限の創出の余錐を供給する。 -/
def algebraColimitCocone : Cocone F where
  pt := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.ofColimitCocone F c hc
  ι.app j := {
    hom := c.ι.app j
    comm n := by
      rw [id_tensorHom]
      exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.colimitAction_ι F c hc n j).symm }
  ι.naturality i j f := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    exact c.ι.naturality f

/-- 概要：底の余極限からの普遍射は代数射（BM §1）。
方針：作用保存を係数付き入力の余極限の構造射の後で判定する。
規約：任意の代数の余錐を入力に取る。
使われ方：持ち上げた余錐の普遍性を示す。 -/
def algebraColimitDesc (s : Cocone F) : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.algebraColimitCocone F c hc).pt ⟶ s.pt where
  hom := hc.desc ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCocone s)
  comm n := by
    change _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.colimitAction F c hc n ≫ hc.desc ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCocone s) =
      (𝟙 (P.arity n) ⊗ₘ _root_.SerrePositivity.TensorPowers.map (hc.desc ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCocone s)) n) ≫
        s.pt.action n
    rw [id_tensorHom]
    apply (isColimitOfPreserves (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.operationInputFunctor (P.arity n) n) hc).hom_ext
    intro j
    change (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (c.ι.app j) n) ≫ _ =
      (P.arity n ◁ _root_.SerrePositivity.TensorPowers.map (c.ι.app j) n) ≫ _
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.colimitAction_ι_assoc, hc.fac,
      ← whiskerLeft_comp_assoc, ← _root_.SerrePositivity.TensorPowers.map_comp, hc.fac]
    erw [(s.ι.app j).comm, id_tensorHom]
    rfl

/-- 概要：底の余極限から持ち上げた代数の余錐は余極限（BM §1）。
方針：普遍射を代数射へ上げ、忘却の忠実性で公式と一意性を移す。
規約：テンソル冪による指定図式の保存だけを使う。
使われ方：忘却関手による余極限の創出を保証する。 -/
def algebraColimitIsColimit : IsColimit (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.algebraColimitCocone F c hc) where
  desc := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.algebraColimitDesc F c hc
  fac s j := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext (hc.fac ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCocone s) j)
  uniq s m h := by
    apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.ext
    apply hc.uniq ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).mapCocone s)
    intro j
    exact congrArg _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.AlgebraHom.hom (h j)

/-- 概要：忘却関手はテンソル冪が保つ底の余極限を作る（BM §1）。
方針：任意の底の余極限錐の持ち上げと同型の反映を使う。
規約：形全体での保存は要求しない。
使われ方：sifted 余極限や忘却後に分裂する coequalizer に適用する。 -/
instance forget_createsColimit : CreatesColimit F (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) :=
  createsColimitOfReflectsIso (fun c hc => {
    liftedCocone := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.algebraColimitCocone F c hc
    validLift := Iso.refl _
    makesColimit := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.algebraColimitIsColimit F c hc })

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

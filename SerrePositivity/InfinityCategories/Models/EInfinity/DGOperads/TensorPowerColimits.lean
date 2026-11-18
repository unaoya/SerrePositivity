module

public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying
public import Mathlib.CategoryTheory.Limits.Sifted
public import Mathlib.CategoryTheory.Limits.Connected

/-!
模型。文献の定義との比較は後で
# 複体のテンソル冪による sifted 余極限の保存

概要：Berger–Moerdijk §1 の有限入力の演算に使うテンソル冪は sifted 余極限を保つ。
方針：テンソルの両変数での余極限保存を、形の対角関手の final 性で制限する。
規約：零次の冪も含む。sifted の非空性は零次の定数関手に必要。
使われ方：代数の余極限と自由像の小対象性を検証する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w v vK uK u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable (J : Type w) [Category.{v} J] [IsSifted J]

attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：有限テンソル冪は sifted な形の余極限を保つ（BM §1）。
方針：零次では連結性、帰納段階では二変数の余極限と final な対角を使う。
規約：形の宇宙は係数環の宇宙から独立。
使われ方：固定 arity の演算の余極限への降下を与える。 -/
lemma tensorPower_preservesSiftedColimits_of_tensor {K : Type uK} [Category.{vK} K]
    [MonoidalCategory K] [∀ Q : K, PreservesColimitsOfShape J (tensorLeft Q)]
    [∀ Q : K, PreservesColimitsOfShape J (tensorRight Q)] (n : ℕ) :
    PreservesColimitsOfShape J (powerFunctor (C := K) n) := by
  induction n with
  | zero =>
    refine ⟨fun {F} => ⟨fun {c} _ => ?_⟩⟩
    exact ⟨isColimitConstCocone J (𝟙_ K)⟩
  | succ n ih =>
    let := ih
    refine ⟨fun {F} => ⟨fun {c} hc => ?_⟩⟩
    have h₂ := isColimitOfPreserves₂ (curriedTensor K) hc
      (isColimitOfPreserves (powerFunctor n) hc)
    have hd := (Functor.Final.isColimitWhiskerEquiv (Functor.diag J) _).symm h₂
    let d := ((curriedTensor K).mapCocone₂ c ((powerFunctor n).mapCocone c)).whisker
      (Functor.diag J)
    let e : (Functor.diag J ⋙ Functor.uncurry.obj
        ((((Functor.whiskeringLeft₂ K).obj F).obj (F ⋙ powerFunctor n)).obj
          (curriedTensor K))) ≅ F ⋙ powerFunctor (n + 1) :=
      NatIso.ofComponents (fun j => Iso.refl _) (by
        intro i j f
        dsimp [powerFunctor]
        simp only [Category.comp_id, Category.id_comp, _root_.SerrePositivity.TensorPowers.map, tensorHom_def])
    exact ⟨(IsColimit.equivOfNatIsoOfIso e d ((powerFunctor (n + 1)).mapCocone c)
      (Cocone.ext (Iso.refl _) (by
        intro j
        dsimp [d, e, powerFunctor, Functor.mapCocone₂]
        simp only [Category.comp_id, _root_.SerrePositivity.TensorPowers.map, tensorHom_def]
        exact Category.id_comp _))).toFun hd⟩

/-- 概要：複体の有限テンソル冪は sifted 余極限を保つ（BM §1）。
方針：閉モノイダル構造の各変数での余極限保存を一般の保存判定へ適用する。
規約：零次の冪を含む。
使われ方：自由代数の底の余極限保存を検証する。 -/
instance tensorPower_preservesSiftedColimits {A : Type u} [CommRing A] (n : ℕ) :
    PreservesColimitsOfShape J (powerFunctor (C := Complex A) n) :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPower_preservesSiftedColimits_of_tensor J n

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

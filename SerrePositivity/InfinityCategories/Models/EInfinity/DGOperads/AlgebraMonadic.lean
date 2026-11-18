module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraColimits
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FreeAlgebraAdjunction
public import Mathlib.CategoryTheory.Monad.Monadicity

/-!
模型。文献の定義との比較は後で
# オペラッド代数の忘却関手のモナド性

概要：Berger–Moerdijk §1 の自由・忘却随伴に Beck のモナド性判定を適用する。
方針：忘却後に分裂する coequalizer は全てのテンソル冪で保存されるので持ち上がる。
規約：任意の対称オペラッドを扱い、モデル構造は使わない。
使われ方：自由代数の表示による一般の余極限を構成する。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}

/-- 概要：忘却後に分裂する対の底の余極限はテンソル冪で保たれる（BM §1）。
方針：分裂 coequalizer の絶対性を図式の標準比較に沿って移す。
規約：零次のテンソル冪も含む。
使われ方：その coequalizer の代数構造を底で構成する。 -/
lemma splitPair_tensorPower_preservesColimit {X Y : P.Algebra} (f g : X ⟶ Y)
    [(_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).IsSplitPair f g] (n : ℕ) :
    PreservesColimit (parallelPair f g ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) (powerFunctor n) := by
  have : HasSplitCoequalizer f.hom g.hom :=
    inferInstanceAs ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).IsSplitPair f g)
  have : PreservesColimit
      (parallelPair ((parallelPair f g ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).map WalkingParallelPairHom.left)
        ((parallelPair f g ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P).map WalkingParallelPairHom.right)) (powerFunctor n) := by
    change PreservesColimit (parallelPair f.hom g.hom) (powerFunctor n)
    infer_instance
  exact preservesColimit_of_iso_diagram (powerFunctor n)
    (diagramIsoParallelPair (parallelPair f g ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P)).symm

/-- 概要：忘却関手は忘却後に分裂する対の coequalizer を作る（BM §1）。
方針：各テンソル冪による保存から底の余極限を持ち上げる。
規約：代数での分裂を要求しない。
使われ方：Beck のモナド性判定の入力となる。 -/
instance forget_createsSplitCoequalizers (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) :
    Monad.CreatesColimitOfIsSplitPair (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) where
  out f g _ := by
    let : ∀ n, PreservesColimit (parallelPair f g ⋙ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) (powerFunctor n) :=
      fun n => _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.splitPair_tensorPower_preservesColimit f g n
    exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget_createsColimit (parallelPair f g)

/-- 概要：オペラッド代数の忘却関手はモナド的右随伴（BM §1）。
方針：既存の自由・忘却随伴と分裂対の coequalizer の創出に Beck の判定を使う。
規約：モデル構造や小対象性を仮定しない。
使われ方：自由代数の表示を一般の余極限と転送に接続する。 -/
instance forget_monadic (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) : MonadicRightAdjoint (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) :=
  Monad.monadicOfCreatesGSplitCoequalizers P.freeAlgebraAdjunction

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

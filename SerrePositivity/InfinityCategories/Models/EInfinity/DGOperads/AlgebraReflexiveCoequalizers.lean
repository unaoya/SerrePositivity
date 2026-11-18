module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraSiftedColimits
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AlgebraMonadic
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ReflexivePairSifted

/-!
模型。文献の定義との比較は後で
# オペラッド代数の reflexive coequalizer

概要：Berger–Moerdijk §1 の代数は reflexive coequalizer を持ち、忘却関手が保つ。
方針：reflexive pair の形の sifted 性と、平行対の包含の final 性を使う。
規約：係数環と代数の cofibrancy を制限しない。
使われ方：随伴持ち上げによる全余極限の構成に用いる。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {A : Type u} [CommRing A] (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A)

/-- 概要：オペラッド代数は reflexive coequalizer を持つ（BM §1）。
方針：底の WalkingReflexivePair 型の余極限を代数へ持ち上げる。
規約：単位と零入力演算を含む全代数を扱う。
使われ方：自由代数の表示を任意の余極限へ接続する。 -/
instance hasReflexiveCoequalizers : HasReflexiveCoequalizers P.Algebra :=
  hasReflexiveCoequalizers_iff.1 inferInstance

/-- 概要：忘却関手は reflexive coequalizer を保つ（BM §1）。
方針：共通切断を付加した図式の保存を final な包含で平行対へ制限する。
規約：個々の対の共通切断が存在すればよい。
使われ方：自由表示の余極限の底を計算する。 -/
instance forget_preservesReflexiveCoequalizers :
    Monad.PreservesColimitOfIsReflexivePair (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) where
  out {_ _} f g _ := by
    have : PreservesColimit
        (WalkingParallelPair.inclusionWalkingReflexivePair ⋙ ofIsReflexivePair f g)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P) := inferInstance
    exact preservesColimit_of_iso_diagram (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra.forget P)
      (inclusionWalkingReflexivePairOfIsReflexivePairIso f g)

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Algebra

module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Morphism
public import SerrePositivity.EInfinity.BarrattEccles.AugmentationComposition

/-!
# Barratt–Eccles から可換オペラッドへの augmentation

概要：Berger–Fresse §1.1 の E → Com を対称 dg オペラッドの射として構成する。
方針：arity ごとの既存の augmentation に自然性、単位と部分合成の保存の証明を付ける。
規約：各成分は鎖ホモトピー同値に由来する擬同型である。
使われ方：可換 A 代数を Barratt–Eccles 代数へ制限し、E∞ 構造を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory HomologicalComplex

variable (A : Type u) [CommRing A]

/-- 概要：Barratt–Eccles の augmentation は対称 dg オペラッドの射である（Berger–Fresse §1.1）。
方針：対称列の自然変換と単位・全ての部分合成の保存を束ねる。
規約：arity 0 を含み、任意の可換基礎環 A に対して定義する。
使われ方：Com 代数の E 代数への制限の係数の射となる。 -/
def augmentation : operad A ⟶ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A where
  map := augmentationSequence A
  unit := unit_augmentation A
  comp := partialComposition_augmentation A

/-- 概要：augmentation の各 arity 成分は既存の複体の augmentation である（Berger–Fresse §1.1）。
方針：オペラッド射と自然変換の定義を展開する。
規約：標準 n 元対象で評価する。
使われ方：成分ごとの可縮性とオペラッド射を接続する。 -/
lemma augmentation_app (n : ℕ) :
    (augmentation A).map.app (FiniteBijection.of n) = complexAugmentation A n := rfl

/-- 概要：E → Com の全ての arity 成分は擬同型である（Berger–Fresse §1.1）。
方針：既存の収縮から得た augmentation の擬同型性を使う。
規約：係数環の標数を制限しない。
使われ方：Barratt–Eccles を可換オペラッドの E∞ 分解として用いる。 -/
lemma augmentation_quasiIso (n : ℕ) :
    QuasiIso ((augmentation A).map.app (FiniteBijection.of n)) :=
  complexAugmentation_quasiIso A n

end SerrePositivity.EInfinity.BarrattEccles

module

public import SerrePositivity.InfinityCategories.F1B.KanInvertibleTargetLiftingIso
public import SerrePositivity.InfinityCategories.F1B.KanInternalHomSwapNaturality
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseHomFiberPostcomposition

/-!
概要：関手の制限による後合成の各 fiber での可逆辺の持ち上げ。
方針：内部 Hom の交換で関手の制限へ移し、fiber の同型で全空間へ戻す。
規約：単射の始域・標的および底には quasicategory 性を課さない。
使われ方：二つの cartesian 輸送の像を同じ底の fiber 内で一致させる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：単射による関手の制限の内部 Hom での後合成は可逆辺を終点指定で持ち上げる。
方針：内部 Hom を交換し、通常の関手の制限の相対可逆 path の充填性を使う。
規約：K と単射 v の両端は任意、値域 X は quasicategory。
使われ方：変動する関手の全空間の fiber の持ち上げ条件。 -/
lemma kanInvertibleTargetLifting_internalHom_pre {P Q X : SSet.{u}}
    [Quasicategory X] (K : SSet.{u}) (v : P ⟶ Q) [Mono v] :
    KanInvertibleTargetLifting ((ihom K).map ((pre v).app X)) := by
  have : TrivialKanFibration (relativeEquivalencePathMapAt
      ((pre v).app ((ihom K).obj X)) 1) :=
    trivialKanFibration_relativeEquivalencePathMapAt_pre v ((ihom K).obj X) 1
  exact (kanInvertibleTargetLifting_of_relativePath ((pre v).app ((ihom K).obj X))).map_iso
    (internalHomSwapIso Q K X) (internalHomSwapIso P K X)
    (kanInternalHomSwap_pre_left v K X).symm

/-- 概要：変動する関手の全空間の後合成は各 fiber で可逆辺を終点指定で持ち上げる。
方針：通常の内部 Hom の持ち上げを後合成を保つ fiber 同型で移送する。
規約：元の射影 p に fibration 性は不要。
使われ方：相対 Kan 比較の標的の cartesian な持ち上げの厳密化。 -/
lemma kanInvertibleTargetLifting_kanFiberwiseHomPostcompFiber {K C P Q X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ C) (c : C _⦋0⦌) (v : P ⟶ Q) [Mono v] :
    KanInvertibleTargetLifting (kanFiberwiseHomPostcompFiber p ((pre v).app X) c) :=
  (kanInvertibleTargetLifting_internalHom_pre (vertexFiber p c) v).map_iso
    (kanFiberwiseHomFiberIso p c ((ihom Q).obj X))
    (kanFiberwiseHomFiberIso p c ((ihom P).obj X))
    (kanFiberwiseHomFiberIso_postcomp p c ((pre v).app X))

end SerrePositivity.InfinityCategories.F1B

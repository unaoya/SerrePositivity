module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathInnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.InnerPullback
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：可逆 path の置換を使った小さい ∞ 圏の引き戻し候補。
方針：第一関手の可逆 path による置換の終点を第二関手に沿って引き戻す。
規約：quasicategory 性と二射影・可換関手同型を構成し、Cat_∞ の普遍性は別に証明する。
使われ方：Cat_∞ の引き戻しと lax pullback の同値辺上の部分圏の比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

variable {A B C : SSet.{u}}

/-- 概要：関手二本の可逆 path を含む引き戻しの単体集合。
方針：可逆 path の置換の終点評価を第二関手で引き戻す。
規約：path の向きは p(a) から q(b)。
使われ方：Cat_∞ の引き戻しを表す候補の具体的な構成。 -/
@[kerodon 032Z]
def catPullback (p : A ⟶ C) (q : B ⟶ C) : SSet.{u} :=
  pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) q

/-- 概要：小さい quasicategory 間の引き戻し候補は quasicategory。
方針：置換の終点評価の inner fibration 性と引き戻しの充填性を使う。
規約：元の関手 p、q に充填性を仮定しない。
使われ方：引き戻し候補を Cat_∞ の対象として束縛する。 -/
@[kerodon 032Z]
instance catPullback_quasicategory (p : A ⟶ C) (q : B ⟶ C)
    [Quasicategory A] [Quasicategory B] [Quasicategory C] : Quasicategory (catPullback p q) :=
  inferInstanceAs (Quasicategory (pullback (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap p) q))

/-- 概要：引き戻し候補を QCat の対象として表示する。
方針：候補の単体集合と証明済みの quasicategory 性を束縛する。
規約：小さい単体の宇宙 u を維持する。
使われ方：候補を coherent nerve の頂点として Cat_∞ に置く。 -/
def catPullbackObject (p : A ⟶ C) (q : B ⟶ C)
    [Quasicategory A] [Quasicategory B] [Quasicategory C] : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  (⟨catPullback p q, inferInstance⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u})

/-- 概要：引き戻し候補から第一の圏への射影。
方針：置換の対象を記憶する射影へ合成する。
規約：可逆 path の始点側の対象を取り出す。
使われ方：Cat_∞ の引き戻し錐の第一の脚。 -/
def catPullbackFst (p : A ⟶ C) (q : B ⟶ C) : catPullback p q ⟶ A :=
  pullback.fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection p

/-- 概要：引き戻し候補から第二の圏への射影。
方針：外側の引き戻しの第二射影を取る。
規約：可逆 path の終点側の対象を取り出す。
使われ方：Cat_∞ の引き戻し錐の第二の脚。 -/
def catPullbackSnd (p : A ⟶ C) (q : B ⟶ C) : catPullback p q ⟶ B := pullback.snd _ _

/-- 概要：引き戻し候補が持つ指定された可逆 path の族。
方針：二重の引き戻しの第一射影で path 成分を取り出す。
規約：両端点の厳密な等式は別の補題で公開する。
使われ方：錐の可換性と全パラメータの普遍的な持ち上げ。 -/
def catPullbackPath (p : A ⟶ C) (q : B ⟶ C) : catPullback p q ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath C :=
  pullback.fst _ _ ≫ pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint C 0) p

/-- 概要：引き戻し候補の二つの脚の像を結ぶ関手同型。
方針：置換の標準関手同型を第一射影で前合成し、引き戻しの等式で終点を合わせる。
規約：可逆 path の向きは第一の脚から第二の脚。
使われ方：Cat_∞ の引き戻し錐の可換性の具体的な証人。 -/
def catPullbackCommutativity (p : A ⟶ C) (q : B ⟶ C) [Quasicategory C] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (catPullbackFst p q ≫ p) (catPullbackSnd p q ≫ q) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementFunctorIso p).precomp (pullback.fst _ _) ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex pullback.condition))

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

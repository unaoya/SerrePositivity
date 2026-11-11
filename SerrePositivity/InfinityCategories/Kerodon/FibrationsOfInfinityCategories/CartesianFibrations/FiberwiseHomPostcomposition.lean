module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseFunctorPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseHomFiberNaturality

/-!
概要：実際の fiber ごとの関手の全空間に標的への後合成を導入する。
方針：一般の変動する局所形の後合成を逆像の関手に適用する。
規約：元の構造射と標的の射は任意。
使われ方：相対 join の族の制限と標的の図式を同時に保つ相対比較。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：fiber ごとの関手を標的の射で後合成する。
方針：逆像の局所形に一般の後合成を適用する。
規約：底の構造射は保つ。
使われ方：全空間の相対余錐の標的での指定。 -/
def fiberwiseHomPostcomp {K C D E : SSet.{u}} (p : K ⟶ C) (U : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom p D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHom p E :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseFunctorPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p) U

/-- 概要：全空間の後合成は底への射影と可換。
方針：一般の後合成の底の保存を使う。
規約：厳密な等式。
使われ方：底上の射と fiber の射の構成。 -/
lemma fiberwiseHomPostcomp_projection {K C D E : SSet.{u}} (p : K ⟶ C) (U : D ⟶ E) :
    fiberwiseHomPostcomp p U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p E =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D := rfl

/-- 概要：全空間の後合成を底 C 上の対象の射として扱う。
方針：底への射影の保存を Over 圏の射の条件に使う。
規約：底は C のまま。
使われ方：相対比較の引き戻しと fiber の計算。 -/
def fiberwiseHomPostcompOver {K C D E : SSet.{u}} (p : K ⟶ C) (U : D ⟶ E) :
    Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) ⟶ Over.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p E) :=
  Over.homMk (fiberwiseHomPostcomp p U) (fiberwiseHomPostcomp_projection p U)

/-- 概要：元の図式の後合成は全空間への curry と可換。
方針：一般の族の後合成の自然性を使う。
規約：底へのパラメータ a は任意。
使われ方：指定された標的の図式を全空間の持ち上げ問題へ写す。 -/
lemma fiberwiseHomCurry_postcomp {K C A D E : SSet.{u}} (p : K ⟶ C)
    (U : D ⟶ E) (a : A ⟶ C) (H : pullback a p ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p a (H ≫ U) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomCurry p a H ≫ fiberwiseHomPostcomp p U :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseFunctorCurry_postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p) U ⟨a, H⟩

/-- 概要：底上の添字の制限は標的への後合成と可換。
方針：逆像の自然変換に対する一般の前後合成の可換性を使う。
規約：i の単射性や fibration 性は不要。
使われ方：全空間の相対比較の可換四角形。 -/
lemma fiberwiseHomPre_postcomp {C D E : SSet.{u}} {K L : Over C}
    (i : K ⟶ L) (U : D ⟶ E) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := D) i ≫ fiberwiseHomPostcomp K.hom U =
      fiberwiseHomPostcomp L.hom U ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomPre (D := E) i :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseFunctorPre_postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMapNat i) U

/-- 概要：全空間の後合成が各頂点の fiber に誘導する射。
方針：底を保つ後合成を fiber の射に制限する。
規約：底の頂点を固定する。
使われ方：通常の内部 Hom の後合成との同定。 -/
def fiberwiseHomPostcompFiber {K C D E : SSet.{u}} (p : K ⟶ C) (U : D ⟶ E)
    (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p D) c ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomProjection p E) c :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap _ _ (fiberwiseHomPostcomp p U) (fiberwiseHomPostcomp_projection p U) c

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FiberwiseFunctorEquiv
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FiberwiseFunctorPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.OverPullbackMorphism
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：fiber ごとの関手の全空間 Fun(K/C,D) と、その底上のパラメータ付き普遍性。
方針：局所形を実際の pullback とし、pullback の余極限保存から族との全単射を得る。
規約：K→C は任意。この段階では cartesian fibration 性を主張しない。
使われ方：Kerodon Lemma 7.3.4.5（Tag 02ZR） の図式の全空間の入力。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：底 C 上で K の逆像を D へ写す関手の全空間。
方針：底の標準単体ごとに、その pullback 上の図式を取る。
規約：全対象の単体の宇宙は u。
使われ方：fiber ごとの普遍余錐を一つの族として組み立てる。 -/
@[kerodon 046N]
def fiberwiseHom {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u}) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p) D

/-- 概要：fiber ごとの関手の全空間から底への射影。
方針：各図式の底の標準単体を取る。
規約：strict な単体集合の射。
使われ方：全空間上の持ち上げと底上の族の比較。 -/
@[kerodon 046N]
def fiberwiseHomProjection {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u}) :
    fiberwiseHom p D ⟶ C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p) D

/-- 概要：底の図式に沿う実際の逆像上の図式から fiber ごとの族を作る。
方針：各標準単体上へ図式を制限して curry する。
規約：固定する底への射は a。
使われ方：元の図式を族としての持ち上げ問題へ変換する。 -/
def fiberwiseHomCurry {K A C D : SSet.{u}} (p : K ⟶ C) (a : A ⟶ C)
    (H : pullback a p ⟶ D) : A ⟶ fiberwiseHom p D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p) ⟨a, H⟩

/-- 概要：図式から作った族は指定した底の図式に重なる。
方針：一般の curry の射影の等式。
規約：同型ではなく射の等式。
使われ方：固定した底の図式を保つ持ち上げ問題。 -/
lemma fiberwiseHomCurry_projection {K A C D : SSet.{u}} (p : K ⟶ C) (a : A ⟶ C)
    (H : pullback a p ⟶ D) : fiberwiseHomCurry p a H ≫ fiberwiseHomProjection p D = a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry_projection (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p) ⟨a, H⟩

/-- 概要：逆像上の図式と指定された底上の fiber ごとの族は全単射。
方針：一般の族の普遍性を実際の pullback 関手に適用し、底を等式で固定する。
規約：全ての単体集合パラメータ A に対する strict な普遍性。
使われ方：族の延長を元の全空間上の図式の延長へ戻す。 -/
@[kerodon 02TP]
def fiberwiseHomEquiv {K A C D : SSet.{u}} (p : K ⟶ C) (a : A ⟶ C) :
    (pullback a p ⟶ D) ≃
      { f : A ⟶ fiberwiseHom p D // f ≫ fiberwiseHomProjection p D = a } where
  toFun H := ⟨fiberwiseHomCurry p a H, fiberwiseHomCurry_projection p a H⟩
  invFun f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorValue
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseFunctorHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p)).symm f.val) f.property
  left_inv H := by
    let F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorValue_pair
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseFunctorHomEquiv F).symm (fiberwiseHomCurry p a H))
      (fiberwiseHomCurry_projection p a H)
    have ht := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseFunctorHomEquiv F).symm_apply_apply
      (⟨a, H⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FiberwiseFunctorSimplex F D A)
    exact eq_of_heq (Sigma.mk.inj (he.trans ht)).2
  right_inv f := by
    apply Subtype.ext
    have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorValue_pair
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseFunctorHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p)).symm f.val) f.property
    exact (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseFunctorCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p)) he).trans
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.fiberwiseFunctorHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p)).apply_symm_apply f.val)

/-- 概要：底上の対象の射が fiber ごとの関手の制限を誘導する。
方針：逆像の自然変換による前合成。
規約：元の底上の射とは反対の向き。
使われ方：錐の全空間から元の図式の全空間への制限。 -/
def fiberwiseHomPre {C D : SSet.{u}} {K L : Over C} (i : K ⟶ L) :
    fiberwiseHom L.hom D ⟶ fiberwiseHom K.hom D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.fiberwiseFunctorPre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackMapNat i)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "B.4.5" (partial := stronger-hyp) "仮定：π:Y→ZをcoCartesian fibration、φを自明な積束Y×D→Y、Dを準圏に限定（Leanが強い：coCartesian π・定数のfiber）。結論：πの各逆像からDへの写像を表す相対指数の射影はCartesian fibrationとなる（この定数束模型でのcategorical fibration保存の強い部分）。一般flat categorical π・任意categorical φの右Quillen性と、右随伴で選んだ依存積との全比較は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.fiberwiseHomEquiv

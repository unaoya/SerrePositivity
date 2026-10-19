module

public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseFunctorEquiv
public import SerrePositivity.InfinityCategories.F1B.KanFiberwiseFunctorPrecomposition
public import SerrePositivity.InfinityCategories.F1.OverPullbackMorphism

/-!
概要：fiber ごとの関手の全空間 Fun(K/C,D) と、その底上のパラメータ付き普遍性。
方針：局所形を実際の pullback とし、pullback の余極限保存から族との全単射を得る。
規約：K→C は任意。この段階では cartesian fibration 性を主張しない。
使われ方：Kerodon Lemma 7.3.4.5 の図式の全空間の入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底 C 上で K の逆像を D へ写す関手の全空間。
方針：底の標準単体ごとに、その pullback 上の図式を取る。
規約：全対象の単体の宇宙は u。
使われ方：fiber ごとの普遍余錐を一つの族として組み立てる。 -/
def kanFiberwiseHom {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u}) : SSet.{u} :=
  kanFiberwiseFunctor (overPullbackUnderlying p) D

/-- 概要：fiber ごとの関手の全空間から底への射影。
方針：各図式の底の標準単体を取る。
規約：strict な単体集合の射。
使われ方：全空間上の持ち上げと底上の族の比較。 -/
def kanFiberwiseHomProjection {K C : SSet.{u}} (p : K ⟶ C) (D : SSet.{u}) :
    kanFiberwiseHom p D ⟶ C := kanFiberwiseFunctorProjection (overPullbackUnderlying p) D

/-- 概要：底の図式に沿う実際の逆像上の図式から fiber ごとの族を作る。
方針：各標準単体上へ図式を制限して curry する。
規約：固定する底への射は a。
使われ方：元の図式を族としての持ち上げ問題へ変換する。 -/
def kanFiberwiseHomCurry {K A C D : SSet.{u}} (p : K ⟶ C) (a : A ⟶ C)
    (H : pullback a p ⟶ D) : A ⟶ kanFiberwiseHom p D :=
  kanFiberwiseFunctorCurry (overPullbackUnderlying p) ⟨a, H⟩

/-- 概要：図式から作った族は指定した底の図式に重なる。
方針：一般の curry の射影の等式。
規約：同型ではなく射の等式。
使われ方：固定した底の図式を保つ持ち上げ問題。 -/
lemma kanFiberwiseHomCurry_projection {K A C D : SSet.{u}} (p : K ⟶ C) (a : A ⟶ C)
    (H : pullback a p ⟶ D) : kanFiberwiseHomCurry p a H ≫ kanFiberwiseHomProjection p D = a :=
  kanFiberwiseFunctorCurry_projection (overPullbackUnderlying p) ⟨a, H⟩

/-- 概要：逆像上の図式と指定された底上の fiber ごとの族は全単射。
方針：一般の族の普遍性を実際の pullback 関手に適用し、底を等式で固定する。
規約：全ての単体集合パラメータ A に対する strict な普遍性。
使われ方：族の延長を元の全空間上の図式の延長へ戻す。 -/
def kanFiberwiseHomEquiv {K A C D : SSet.{u}} (p : K ⟶ C) (a : A ⟶ C) :
    (pullback a p ⟶ D) ≃
      { f : A ⟶ kanFiberwiseHom p D // f ≫ kanFiberwiseHomProjection p D = a } where
  toFun H := ⟨kanFiberwiseHomCurry p a H, kanFiberwiseHomCurry_projection p a H⟩
  invFun f := kanFiberwiseFunctorValue
    ((kanFiberwiseFunctorHomEquiv (overPullbackUnderlying p)).symm f.val) f.property
  left_inv H := by
    let F := overPullbackUnderlying p
    have he := kanFiberwiseFunctorValue_pair
      ((kanFiberwiseFunctorHomEquiv F).symm (kanFiberwiseHomCurry p a H))
      (kanFiberwiseHomCurry_projection p a H)
    have ht := (kanFiberwiseFunctorHomEquiv F).symm_apply_apply
      (⟨a, H⟩ : KanFiberwiseFunctorSimplex F D A)
    exact eq_of_heq (Sigma.mk.inj (he.trans ht)).2
  right_inv f := by
    apply Subtype.ext
    have he := kanFiberwiseFunctorValue_pair
      ((kanFiberwiseFunctorHomEquiv (overPullbackUnderlying p)).symm f.val) f.property
    exact (congrArg (kanFiberwiseFunctorCurry (overPullbackUnderlying p)) he).trans
      ((kanFiberwiseFunctorHomEquiv (overPullbackUnderlying p)).apply_symm_apply f.val)

/-- 概要：底上の対象の射が fiber ごとの関手の制限を誘導する。
方針：逆像の自然変換による前合成。
規約：元の底上の射とは反対の向き。
使われ方：錐の全空間から元の図式の全空間への制限。 -/
def kanFiberwiseHomPre {C D : SSet.{u}} {K L : Over C} (i : K ⟶ L) :
    kanFiberwiseHom L.hom D ⟶ kanFiberwiseHom K.hom D :=
  kanFiberwiseFunctorPre (overPullbackMapNat i)

end SerrePositivity.InfinityCategories

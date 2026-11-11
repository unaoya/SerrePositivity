module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.PairingHorns
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
概要：最後の端点を含む prism の右 anodyne 性。
方針：境界との積の正則 pairing と内部 Hom の随伴で任意の単射へ広げる。
規約：モデル構造を用いず左右のホーンの llp と rlp を使う。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153）、Lemma 4.4.2.15（Tag 01A7）。

対応節は Kerodon 4.4（Tag 01EM）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

/-- 概要：最後の一次ホーンと任意の単射の pushout-product は right anodyne。
方針：内部 Hom の相対射の rlp を境界で検査し、既知の積の pairing に帰着する。
規約：第一因子は Λ[1,1] から Δ[1]。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153）、Lemma 4.4.2.15（Tag 01A7） の境界のホモトピー。 -/
lemma rightAnodyneExtensions_pushoutObjObj_point {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : (curriedTensor SSet.{u}).PushoutObjObj (horn 1 1).ι i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions sq.ι := by
  intro E D p hp
  let sq' := Functor.PullbackObjObj.ofHasPullback internalHom (horn 1 1).ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  suffices (monomorphisms SSet.{u}).rlp sq'.π from this _ inferInstance
  rw [SSet.rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Subcomplex.unionProd.pushoutObjObj.{u} (horn 1 1) (boundary n)) sq',
    Subcomplex.unionProd.pushoutObjObj_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions_unionProd_point n p hp

/-- 概要：最後の一次ホーンの包含と任意の単体集合の積は right anodyne。
方針：空集合からの単射との pushout-product を用いる。
規約：終端の端点から prism 全体への射。
使われ方：Kerodon Lemma 4.4.2.15（Tag 01A7） の右ファイブレーションへの持ち上げ。 -/
lemma rightAnodyneExtensions_point_whiskerRight (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions ((horn 1 1).ι ▷ A) :=
  rightAnodyneExtensions_pushoutObjObj_point (initial.to A)
    (.ofIsInitialRight (curriedTensor _) (horn 1 1).ι (initial.to A) initialIsInitial)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations

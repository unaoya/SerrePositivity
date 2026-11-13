module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.PairingHorns
public import Mathlib.AlgebraicTopology.SimplicialSet.PushoutProduct
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
public import Mathlib.CategoryTheory.LiftingProperties.ParametrizedAdjunction
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
概要：最初の端点を含む prism の left anodyne 性。
方針：境界との積の正則 pairing と内部 Hom の随伴で任意の単射へ広げる。
規約：モデル構造を用いず左右のホーンの llp と rlp を使う。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153）、Lemma 4.4.2.15（Tag 01A7）。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：最初の一次ホーンと任意の単射の pushout-product は left anodyne。
方針：内部 Hom の相対射の rlp を境界で検査し、既知の積の pairing に帰着する。
規約：第一因子は Λ[1,0] から Δ[1]。
使われ方：Kerodon Proposition 4.2.5.3（Tag 0153）、Lemma 4.4.2.15（Tag 01A7） の境界のホモトピー。 -/
lemma leftAnodyneExtensions_pushoutObjObj_point {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (sq : (curriedTensor SSet.{u}).PushoutObjObj (horn 1 0).ι i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions sq.ι := by
  intro E D p hp
  let sq' := Functor.PullbackObjObj.ofHasPullback internalHom (horn 1 0).ι p
  rw [internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  suffices (monomorphisms SSet.{u}).rlp sq'.π from this _ inferInstance
  rw [SSet.rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff
    (Subcomplex.unionProd.pushoutObjObj.{u} (horn 1 0) (boundary n)) sq',
    Subcomplex.unionProd.pushoutObjObj_ι]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_unionProd (0 : Fin 1) n p hp

/-- 概要：最初の一次ホーンの包含と任意の単体集合の積は left anodyne。
方針：空集合からの単射との pushout-product を用いる。
規約：先頭の端点から prism 全体への射。
使われ方：Kerodon §5.3.7（Tag 01US） の left fibration への持ち上げ。 -/
lemma leftAnodyneExtensions_point_whiskerRight (A : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions ((horn 1 0).ι ▷ A) :=
  leftAnodyneExtensions_pushoutObjObj_point (initial.to A)
    (.ofIsInitialRight (curriedTensor _) (horn 1 0).ι (initial.to A) initialIsInitial)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.1.2.6" (partial := direction) "仮定：任意の単射 i と始端の包含（HTT の第三生成系と一致）。結論：その pushout-product は left anodyne、したがって第三生成系の弱飽和閉包は第一の閉包に含まれるという一方向に一致。逆の包含はなく、三生成系の閉包が等しいとは判定しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_point

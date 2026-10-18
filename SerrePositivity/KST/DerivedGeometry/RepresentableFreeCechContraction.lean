module

public import SerrePositivity.KST.DerivedGeometry.RepresentableOpenCechContraction
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Homology.SingleHomology

/-!
概要：表現可能関手と自由加群で評価した局所 Čech 鎖複体の収縮。
方針：被覆元への射から構成した追加退化を共変な自由加群評価へ写す。
規約：係数環の可換性や平坦性は要求しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の自由 Čech 分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (R : Type u) [Ring R] {X : Type u} [TopologicalSpace X]
  {ι : Type u} (U : ι → Opens X) (V : Opens X) (hU : ∀ i, U i ≤ V) (W : Opens X)

/--
概要：W からの Hom と自由 R 加群で評価した増大 Čech 対象。
方針：形式的余積を Hom へ写し、自由加群による共変な評価を行う。
規約：増大先は Hom(W,V) の自由加群の一元余積。
使われ方：TT §3、Toën §3.2 の自由 Čech の局所計算。
-/
def representableFreeCechAugmented : SimplicialObject.Augmented (ModuleCat.{u} R) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj
    ((FormalCoproduct.eval (Type u) (ModuleCat.{u} R)).obj (ModuleCat.free R))).obj
      (((SimplicialObject.Augmented.whiskering _ _).obj
        (formalCoproductMapFunctor (coyoneda.obj (.op W)))).obj
          (boundedOpenCechAugmented U V hU))

/--
概要：W が被覆元に含まれると自由加群で評価した Čech に追加退化がある。
方針：表現可能関手の追加退化を自由加群の共変な評価へ写す。
規約：収縮の存在を仮定せず構成する。
使われ方：TT §3・§8、Toën §3.2 の局所自由 Čech 収縮。
-/
def representableFreeCechExtraDegeneracy (j : ι) (hWj : W ≤ U j) :
    (representableFreeCechAugmented R U V hU W).ExtraDegeneracy :=
  (representableOpenCechExtraDegeneracy U V hU W j hWj).map
    ((FormalCoproduct.eval (Type u) (ModuleCat.{u} R)).obj (ModuleCat.free R))

/--
概要：W が被覆元に含まれると自由 Čech 鎖複体は全正次数で完全。
方針：追加退化が与える単一項複体とのホモトピー同値を使う。
規約：全次数で実際の交代面微分を扱う。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の自由 Čech 分解。
-/
lemma representableFreeCech_exactAt (j : ι) (hWj : W ≤ U j) (n : ℕ) :
    (AlgebraicTopology.AlternatingFaceMapComplex.obj
      (representableFreeCechAugmented R U V hU W).left).ExactAt (n + 1) := by
  let e := (representableFreeCechExtraDegeneracy R U V hU W j hWj).homotopyEquiv
  exact (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mpr
    (ChainComplex.exactAt_succ_single_obj _ n)

end SerrePositivity.KST.DerivedGeometry

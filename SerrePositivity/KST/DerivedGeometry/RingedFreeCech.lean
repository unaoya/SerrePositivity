module

public import SerrePositivity.KST.DerivedGeometry.RingedForgetExact
public import SerrePositivity.KST.DerivedGeometry.AbSheafificationLocalExact
public import SerrePositivity.KST.DerivedGeometry.FreeSheafCechAugmentation

/-!
概要：任意の環層の自由 Yoneda 加群の増大 Čech の局所完全性。
方針：各開 W で B(W) 上の自由 Čech と比較し、実際の追加退化で収縮する。
規約：対象の環層を固定環や平坦な環層へ置換しない。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の係数版アフィン消滅。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (X : TopCat.{u}) (B : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {ι : Type u} (U : ι → Opens X) (V : Opens X) (hU : ∀ i, U i ≤ V)

/--
概要：環層上の自由 Yoneda 加群前層による増大 Čech 単体対象。
方針：形式的な開の増大 Čech を自由前層の関手で評価する。
規約：増大先は V の一元余積。
使われ方：TT §3・§8、Toën §3.2 の環層係数の自由分解。
-/
def ringedFreePresheafCechAugmented : SimplicialObject.Augmented (PresheafOfModules.{u} B.obj) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj
    ((FormalCoproduct.eval (Opens X) (PresheafOfModules.{u} B.obj)).obj
      (ringedFreePresheafOnOpen X B))).obj (boundedOpenCechAugmented U V hU)

/--
概要：自由加群前層の増大 Čech を W で評価したものは B(W) 上の表現可能自由 Čech と同型。
方針：余積評価の自然比較を増大単体対象全体に適用する。
規約：増大と全ての面・退化を保持する。
使われ方：TT §3、Toën §3.2 の係数局所収縮。
-/
def ringedFreePresheafCechEvaluationIso (W : Opens X) :
    ((SimplicialObject.Augmented.whiskering _ _).obj
      (PresheafOfModules.evaluation B.obj (.op W))).obj
        (ringedFreePresheafCechAugmented X B U V hU) ≅
      representableFreeCechAugmented (B.obj.obj (.op W)) U V hU W :=
  ((SimplicialObject.Augmented.whiskering _ _).mapIso
    (ringedFreeFormalPresheafEvaluationIso X B W)).app (boundedOpenCechAugmented U V hU)

/--
概要：W が被覆元に含まれると環層係数の自由 Čech の評価は追加退化を持つ。
方針：既証の表現可能自由 Čech の追加退化を評価同型で移す。
規約：平坦性や分解の存在を新たな仮定にしない。
使われ方：TT §3、Toën §3.2 の局所的な自由 Čech 収縮。
-/
def ringedFreePresheafCechEvaluatedExtraDegeneracy (W : Opens X) (j : ι) (hWj : W ≤ U j) :
    (((SimplicialObject.Augmented.whiskering _ _).obj
      (PresheafOfModules.evaluation B.obj (.op W))).obj
        (ringedFreePresheafCechAugmented X B U V hU)).ExtraDegeneracy :=
  .ofIso (ringedFreePresheafCechEvaluationIso X B U V hU W).symm
    (representableFreeCechExtraDegeneracy (B.obj.obj (.op W)) U V hU W j hWj)

/--
概要：環層係数の自由 Yoneda 加群の増大 Čech 鎖複体。
方針：実際の増大交代面鎖複体を取る。
規約：元の第n項は第n+1項へ移る。
使われ方：TT §3・§8、Toën §3.2 の環層係数の分解。
-/
def ringedFreePresheafAugmentedCechComplex : ChainComplex (PresheafOfModules.{u} B.obj) ℕ :=
  augmentedAlternatingFaceComplex (ringedFreePresheafCechAugmented X B U V hU)

/--
概要：被覆元内の開で評価した環層係数の自由増大 Čech は全次数で完全。
方針：追加退化の収縮と増大鎖複体の評価比較を使う。
規約：零次数の全射性も含めて証明する。
使われ方：TT §3・§8、Toën §3.2 の実際の係数分解の局所完全性。
-/
lemma ringedFreePresheafAugmentedCech_evaluated_exactAt
    (W : Opens X) (j : ι) (hWj : W ≤ U j) (n : ℕ) :
    (((PresheafOfModules.evaluation B.obj (.op W)).mapHomologicalComplex (.down ℕ)).obj
      (ringedFreePresheafAugmentedCechComplex X B U V hU)).ExactAt n := by
  have h := augmentedAlternatingFace_acyclic
    (ringedFreePresheafCechEvaluatedExtraDegeneracy X B U V hU W j hWj) n
  exact (exactAt_iff_of_quasiIsoAt
    (augmentedAlternatingFaceMapIso (PresheafOfModules.evaluation B.obj (.op W))
      (ringedFreePresheafCechAugmented X B U V hU)).hom n).mpr h

end SerrePositivity.KST.DerivedGeometry

module

public import SerrePositivity.KST.DerivedGeometry.FreeSheafOnOpen
public import SerrePositivity.KST.DerivedGeometry.FormalCoproductEvalCovariant
public import SerrePositivity.KST.DerivedGeometry.RepresentableFreeCechContraction
public import SerrePositivity.KST.DerivedGeometry.AlternatingFaceFunctor

/-!
概要：自由加群前層の実際の Čech 鎖複体と開上での評価の比較。
方針：余積評価の比較と表現可能関手の積比較を増大 Čech に適用する。
規約：交代面微分・増大・全ての次数を保持する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の自由 Čech 分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits TopologicalSpace
namespace SerrePositivity.KST.DerivedGeometry
variable (R : Type u) [Ring R] (X : TopCat.{u})

/--
概要：開の自由加群前層の W 上の評価は Hom(W,-) の自由加群と自然同型。
方針：Yoneda の評価と共変 Hom の定義を同じ射で比較する。
規約：開の全包含について自然。
使われ方：TT §3、Toën §3.2 の自由 Čech の局所計算。
-/
def freeModulePresheafEvaluationIso (W : Opens X) :
    freeModulePresheafOnOpen R X ⋙ (evaluation _ _).obj (.op W) ≅
      coyoneda.obj (.op W) ⋙ ModuleCat.free R :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/--
概要：形式的余積の自由前層の W 上の評価を表現可能関手の自由評価へ比較する。
方針：余積保存による評価比較と Yoneda の評価比較を合成する。
規約：全ての形式的余積の射に対する自然同型。
使われ方：TT §3・§8、Toën §3.2 の Čech 評価。
-/
def freeFormalPresheafEvaluationIso (W : Opens X) :
    (FormalCoproduct.eval (Opens X) ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
        (freeModulePresheafOnOpen R X) ⋙ (evaluation _ _).obj (.op W) ≅
      formalCoproductMapFunctor (coyoneda.obj (.op W)) ⋙
        (FormalCoproduct.eval (Type u) (ModuleCat.{u} R)).obj (ModuleCat.free R) :=
  formalCoproductEvalCovariantIso (freeModulePresheafOnOpen R X)
      ((evaluation _ _).obj (.op W)) ≪≫
    (FormalCoproduct.eval (Opens X) (ModuleCat.{u} R)).mapIso
      (freeModulePresheafEvaluationIso R X W)

variable {ι : Type u} (U : ι → Opens X) (V : Opens X) (hU : ∀ i, U i ≤ V)

/--
概要：自由加群前層を用いた増大 Čech 対象。
方針：各有限交叉の自由前層の余積で形式的 Čech 対象を評価する。
規約：増大は元の包含から定まる。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 鎖複体。
-/
def freePresheafCechAugmented :
    SimplicialObject.Augmented ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) :=
  ((SimplicialObject.Augmented.whiskering _ _).obj
    ((FormalCoproduct.eval (Opens X) ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R)).obj
      (freeModulePresheafOnOpen R X))).obj (boundedOpenCechAugmented U V hU)

/--
概要：自由前層の Čech 対象の W 上の評価は表現可能自由 Čech 対象と同型。
方針：形式的余積の評価比較を増大単体対象の全体へ適用する。
規約：増大も含めて自然に比較する。
使われ方：TT §3、Toën §3.2 の局所収縮の移送。
-/
def freePresheafCechEvaluationIso (W : Opens X) :
    ((SimplicialObject.Augmented.whiskering _ _).obj
      ((evaluation _ (ModuleCat.{u} R)).obj (.op W))).obj
        (freePresheafCechAugmented R X U V hU) ≅
      representableFreeCechAugmented R U V hU W :=
  ((SimplicialObject.Augmented.whiskering _ _).mapIso
    (freeFormalPresheafEvaluationIso R X W)).app (boundedOpenCechAugmented U V hU)

/--
概要：自由前層の Čech の W 上の評価は被覆元に含まれれば追加退化を持つ。
方針：構成済みの評価同型で表現可能自由 Čech の追加退化を移す。
規約：元の自由前層の Čech 対象の評価についての構成。
使われ方：TT §3・§8、Toën §3.2 の局所 Čech 収縮。
-/
def freePresheafCechEvaluatedExtraDegeneracy (W : Opens X) (j : ι) (hWj : W ≤ U j) :
    (((SimplicialObject.Augmented.whiskering _ _).obj
      ((evaluation _ (ModuleCat.{u} R)).obj (.op W))).obj
        (freePresheafCechAugmented R X U V hU)).ExtraDegeneracy :=
  .ofIso (freePresheafCechEvaluationIso R X U V hU W).symm
    (representableFreeCechExtraDegeneracy R U V hU W j hWj)

/--
概要：自由加群前層による実際の Čech 鎖複体。
方針：増大単体対象の交代面鎖複体を取る。
規約：元の全ての次数と符号を保持する。
使われ方：TT §3・§8、BvdB Thm 3.1.1、Toën §3.2 の自由 Čech 分解。
-/
def freePresheafCechComplex : ChainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{u} R) ℕ :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj (freePresheafCechAugmented R X U V hU).left

/--
概要：自由前層の Čech 鎖複体の評価は被覆元に含まれる開で正次数で完全。
方針：交代面鎖複体と評価の比較を介して追加退化の収縮を移す。
規約：有限和の微分をそのまま比較し、切断の右完全性は要求しない。
使われ方：TT §3・§8、Toën §3.2 の自由 Čech 分解の局所完全性。
-/
lemma freePresheafCech_evaluated_exactAt (W : Opens X) (j : ι) (hWj : W ≤ U j) (n : ℕ) :
    ((((evaluation _ (ModuleCat.{u} R)).obj (.op W)).mapHomologicalComplex (.down ℕ)).obj
      (freePresheafCechComplex R X U V hU)).ExactAt (n + 1) := by
  let e := (freePresheafCechEvaluatedExtraDegeneracy R X U V hU W j hWj).homotopyEquiv
  have h := (exactAt_iff_of_quasiIsoAt e.hom (n + 1)).mpr
    (ChainComplex.exactAt_succ_single_obj _ n)
  exact (exactAt_iff_of_quasiIsoAt
    ((alternatingFaceCompMapIso ((evaluation _ _).obj (.op W))).app
      (freePresheafCechAugmented R X U V hU).left).hom (n + 1)).mpr h

end SerrePositivity.KST.DerivedGeometry

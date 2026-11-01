module

public import SerrePositivity.DifferentialGraded.Functor.ModuleConeIso
public import SerrePositivity.DifferentialGraded.Tensor.Graded
public import SerrePositivity.DifferentialGraded.Tensor.Enriched
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import SerrePositivity.DifferentialGraded.Module.LeftQuasiIso
public import SerrePositivity.DifferentialGraded.Module.Acyclic
public import SerrePositivity.DifferentialGraded.Module.LeftZero
public import SerrePositivity.DifferentialGraded.Functor.ModuleShift
public import SerrePositivity.DifferentialGraded.Module.ShiftCoherence
public import SerrePositivity.DifferentialGraded.Module.LeftQuasiIsoInverse
public import SerrePositivity.DifferentialGraded.Tensor.Associator.Pentagon
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.DifferentialGraded.Bimodule.Value
public import SerrePositivity.DifferentialGraded.Tensor.Bimodule.Actions

/-!
# Tensor.Bimodule.KFlatness

## 概要
相対 K-flat 性、cone・shift 閉性と擬同型保存をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## Cone（旧 SerrePositivity/DifferentialGraded/Tensor/Cone.lean） -/

/-! # balanced tensorによる標準cone保存と相対K-flatのcone閉性 -/

@[expose] public section Cone
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def rightTensorConeIso (L : LeftModule A D) {M N : ModuleCategory A D} (f : M ⟶ N) :
    mappingCone ((rightTensorFunctor A D L).map f) ≅
      (rightTensorFunctor A D L).obj (moduleCone A D f) := by
  have h : ((rightTensorDG A D L).toComplexFunctor A).map f =
      (rightTensorFunctor A D L).map f := rightTensorDG_map A D L f
  exact eqToIso (congrArg
    (fun g : (rightTensorFunctor A D L).obj M ⟶ (rightTensorFunctor A D L).obj N => mappingCone g)
    h.symm) ≪≫ DGFunctor.moduleConeImageIso A D (rightTensorDG A D L) f

end BalancedTensor

open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 相対K-flat加群は任意の標準coneで閉じる。 -/
lemma moduleRelativeKFlat_cone {M N : ModuleCategory A D} (f : M ⟶ N)
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N)) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (moduleCone A D f)) := by
  intro L hL
  exact cochainAcyclic_of_iso
    (cochainAcyclic_mappingCone ((BalancedTensor.rightTensorFunctor A D L).map f)
      (hM L hL) (hN L hL)) (BalancedTensor.rightTensorConeIso A D L f)

end SerrePositivity.DifferentialGraded
end

end Cone

/-! ## QuasiIsoLeft（旧 SerrePositivity/DifferentialGraded/Tensor/QuasiIsoLeft.lean） -/

/-! # 相対K-flat性による左加群変数の準同型保存 -/

@[expose] public section QuasiIsoLeft
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左右同値と符号付き交換を通じた、opposite上でのacyclic試験。 -/
lemma moduleRelativeKFlat_opposite_test (M : RightModule A D)
    (hM : moduleRelativeKFlat A D M) (C : ModuleCategory A Dᵒᵖ)
    (hC : moduleAcyclic A Dᵒᵖ C) :
    ((BalancedTensor.rightTensorFunctor A Dᵒᵖ M.toFunctor).obj C).Acyclic := by
  let E := leftRightOppositeEquivalence A D
  let L := E.inverse.obj C
  let e : E.functor.obj L ≅ C := E.counitIso.app C
  have hL : leftModuleAcyclic A D (ForgetEnrichment.to (Complex A) L) := by
    intro x n
    exact (hC (op x) n).of_iso ((moduleEvaluation A Dᵒᵖ (op x)).mapIso e.symm)
  exact cochainAcyclic_of_iso (hM (ForgetEnrichment.to (Complex A) L) hL)
    (BalancedTensor.swapIso A D M (ForgetEnrichment.to (Complex A) L) ≪≫
      (BalancedTensor.rightTensorFunctor A Dᵒᵖ M.toFunctor).mapIso e)

/-- 相対K-flat右加群とのtensorは左加群の指定準同型を保存する。 -/
lemma moduleRelativeKFlat_preserves_leftQuasiIso (M : RightModule A D)
    (hM : moduleRelativeKFlat A D M) {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : leftModuleQuasiIso A D g) :
    QuasiIso ((BalancedTensor.leftTensorFunctor A D M).map g) := by
  let G : LeftModuleCategory A D ⥤ ModuleCategory A Dᵒᵖ := leftModuleToRightOpposite A D
  let T : ModuleCategory A Dᵒᵖ ⥤ Complex A := BalancedTensor.rightTensorFunctor A Dᵒᵖ M.toFunctor
  have hc : moduleAcyclic A Dᵒᵖ (moduleCone A Dᵒᵖ (G.map g)) :=
    (moduleQuasiIso_iff_acyclic_cone A Dᵒᵖ (G.map g)).1 hg
  have ht : (T.obj (moduleCone A Dᵒᵖ (G.map g))).Acyclic :=
    moduleRelativeKFlat_opposite_test A D M hM _ hc
  have hq : QuasiIso (T.map (G.map g)) :=
    (complex_quasiIso_iff_acyclic_cone A _).2
      (cochainAcyclic_of_iso ht (BalancedTensor.rightTensorConeIso A Dᵒᵖ M.toFunctor
        (G.map g)).symm)
  let e : BalancedTensor.leftTensorFunctor A D M ≅ G ⋙ T := BalancedTensor.leftTensorSwapIso A D M
  have he : e.hom.app L ≫ T.map (G.map g) ≫ e.inv.app L' =
      (BalancedTensor.leftTensorFunctor A D M).map g := NatIso.naturality_2 e g
  rw [← he]
  infer_instance

end SerrePositivity.DifferentialGraded
end

end QuasiIsoLeft

/-! ## KFlatCriterion（旧 SerrePositivity/DifferentialGraded/Tensor/KFlatCriterion.lean） -/

/-! # 相対K-flat性と左準同型保存の同値 -/

@[expose] public section KFlatCriterion
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
open scoped ZeroObject
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左のacyclic消滅条件は、任意の指定準同型の保存と同値。 -/
lemma moduleRelativeKFlat_iff_preserves_leftQuasiIso (M : RightModule A D) :
    moduleRelativeKFlat A D M ↔
      ∀ {L L' : LeftModuleCategory A D} (g : L ⟶ L'), leftModuleQuasiIso A D g →
        QuasiIso ((BalancedTensor.leftTensorFunctor A D M).map g) := by
  constructor
  · intro h L L' g hg
    exact moduleRelativeKFlat_preserves_leftQuasiIso A D M h g hg
  · intro h L hL
    let N := ForgetEnrichment.of (Complex A) L
    let Z := leftModuleZero A D
    let g : N ⟶ Z := 0
    have hg : leftModuleQuasiIso A D g := by
      apply (leftModuleQuasiIso_iff A D g).2
      intro x
      have hz : ((leftModuleEvaluation A D x).obj Z).Acyclic :=
        acyclic_of_isZero _ (leftModuleZero_evaluation_isZero A D x)
      exact ⟨fun n => (quasiIsoAt_iff_exactAt' _ n (hz n)).2 (hL x n)⟩
    have hq := h g hg
    have hz : ((BalancedTensor.leftTensorFunctor A D M).obj Z).Acyclic :=
      acyclic_of_isZero _ ((BalancedTensor.leftTensorFunctor A D M).map_isZero
        (leftModuleZero_isZero A D))
    intro n
    exact (exactAt_iff_of_quasiIsoAt ((BalancedTensor.leftTensorFunctor A D M).map g) n).2 (hz n)

/-- 零右加群は任意のacyclic左加群とのtensorで消える。 -/
lemma moduleRelativeKFlat_zero : moduleRelativeKFlat A D (zeroModule A D) := by
  intro L _
  exact acyclic_of_isZero _ ((BalancedTensor.rightTensorFunctor A D L).map_isZero
    (moduleZero_isZero A D))

end SerrePositivity.DifferentialGraded
end

end KFlatCriterion

/-! ## Shift（旧 SerrePositivity/DifferentialGraded/Tensor/Shift.lean） -/

/-! # balanced tensorの右加群shift比較と相対K-flatのshift閉性 -/

@[expose] public section Shift
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 実際のbalanced tensorは右加群の整数shiftを通常の複体shiftへ送る。 -/
def rightTensorShiftIso (L : LeftModule A D) (s : ℤ) (M : RightModule A D) :
    obj A D (shiftModule s M) L ≅ (obj A D M L)⟦s⟧ :=
  DGFunctor.moduleShiftImageIso A D (rightTensorDG A D L) s M

end BalancedTensor

open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 任意整数shiftは相対K-flat性を保つ。 -/
lemma moduleRelativeKFlat_shift {M : RightModule A D} (hM : moduleRelativeKFlat A D M) (s : ℤ) :
    moduleRelativeKFlat A D (shiftModule s M) := by
  intro L hL
  exact cochainAcyclic_of_iso (cochainAcyclic_shift (hM L hL) s)
    (BalancedTensor.rightTensorShiftIso A D L s M).symm

/-- 閉零加群圏の既存HasShiftについても同じ閉性が成り立つ。 -/
lemma moduleRelativeKFlat_shiftObj {M : ModuleCategory A D}
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M)) (s : ℤ) :
    moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) (M⟦s⟧)) :=
  moduleRelativeKFlat_shift A D hM s

end SerrePositivity.DifferentialGraded
end

end Shift

/-! ## LeftKFlatResolution（旧 SerrePositivity/DifferentialGraded/Tensor/LeftKFlatResolution.lean） -/

/-! # opposite上の相対K-flat性による左加群のK-flat解像度

## 概要
opposite上の相対K-flat性による左加群のK-flat解像度。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/KFlatComparison.lean。局所導来合成の計算部品、一般Morita・
相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section LeftKFlatResolution
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 左加群の相対K-flat性を、opposite上の右加群の条件として固定する。 -/
def leftModuleRelativeKFlat (L : LeftModule A D) : Prop :=
  moduleRelativeKFlat A Dᵒᵖ L.toRightOpposite

/-- 左K-flatな因子とのtensorは、右変数の任意の準同型を保存する。 -/
lemma leftModuleRelativeKFlat_preserves_rightQuasiIso (L : LeftModule A D)
    (hL : leftModuleRelativeKFlat A D L) {M N : ModuleCategory A D} (f : M ⟶ N)
    (hf : moduleQuasiIso A D f) :
    QuasiIso ((BalancedTensor.rightTensorFunctor A D L).map f) := by
  have hc := (moduleQuasiIso_iff_acyclic_cone A D f).1 hf
  have hleft : leftModuleAcyclic A Dᵒᵖ
      (ForgetEnrichment.to (Complex A) (moduleCone A D f)).toFunctor :=
    fun x => hc x.unop
  have ht := hL (ForgetEnrichment.to (Complex A) (moduleCone A D f)).toFunctor hleft
  have ho := cochainAcyclic_of_iso ht
    (BalancedTensor.swapIso A D (ForgetEnrichment.to (Complex A) (moduleCone A D f)) L).symm
  exact (complex_quasiIso_iff_acyclic_cone A _).2
    (cochainAcyclic_of_iso ho (BalancedTensor.rightTensorConeIso A D L f).symm)

/-- 任意の左加群に対し、右側のcell解像度を既存左右同値で移送する。 -/
theorem exists_leftRelativeKFlat_resolution (N : LeftModuleCategory A D) :
    ∃ (L : LeftModuleCategory A D) (q : L ⟶ N),
      leftModuleRelativeKFlat A D (ForgetEnrichment.to (Complex A) L) ∧
        leftModuleQuasiIso A D q := by
  let E := leftRightOppositeEquivalence A D
  obtain ⟨P, q, _, hP, _, hq⟩ := exists_relativeKFlat_resolution A Dᵒᵖ (E.functor.obj N)
  refine ⟨E.inverse.obj P, E.inverse.map q ≫ (E.unitIso.app N).inv, ?_, ?_⟩
  · exact moduleRelativeKFlat_of_iso A Dᵒᵖ (E.counitIso.app P) hP
  · exact (leftModuleQuasiIso A D).comp_mem _ _
      ((leftRightOpposite_inverse_quasiIso_iff A D q).2 hq)
      ((leftModuleQuasiIso A D).of_isIso _)

end SerrePositivity.DifferentialGraded
end

end LeftKFlatResolution

/-! ## KFlatComparison（旧 SerrePositivity/DifferentialGraded/Tensor/KFlatComparison.lean） -/

/-! # 相対K-flat右加群間の準同型のtensorによる保存

## 概要
相対K-flat右加群間の準同型のtensorによる保存。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/BimoduleKFlatQuasiIso.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section KFlatComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 両端の右相対K-flat性があれば、左因子に条件を課さず準同型を保存する。 -/
lemma rightTensor_relativeKFlat_quasiIso (L : LeftModule A D) {M N : ModuleCategory A D}
    (hM : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) M))
    (hN : moduleRelativeKFlat A D (ForgetEnrichment.to (Complex A) N))
    (f : M ⟶ N) (hf : moduleQuasiIso A D f) :
    QuasiIso ((rightTensorFunctor A D L).map f) := by
  obtain ⟨P, q, hP, hq⟩ := exists_leftRelativeKFlat_resolution A D
    (ForgetEnrichment.of (Complex A) L)
  let τ := rightTensorLeftMap A D q
  have htop : QuasiIso
      ((rightTensorFunctor A D (ForgetEnrichment.to (Complex A) P)).map f) :=
    leftModuleRelativeKFlat_preserves_rightQuasiIso A D
      (ForgetEnrichment.to (Complex A) P) hP f hf
  have hleft : QuasiIso (τ.app M) := moduleRelativeKFlat_preserves_leftQuasiIso A D
    (ForgetEnrichment.to (Complex A) M) hM q hq
  have hright : QuasiIso (τ.app N) := moduleRelativeKFlat_preserves_leftQuasiIso A D
    (ForgetEnrichment.to (Complex A) N) hN q hq
  have hcomp : QuasiIso (τ.app M ≫ (rightTensorFunctor A D L).map f) := by
    exact (τ.naturality f) ▸ (quasiIso_comp _ _)
  exact quasiIso_of_comp_left (τ.app M) _

end SerrePositivity.DifferentialGraded.BalancedTensor
end

end KFlatComparison

/-! ## ProjectiveLeftQuasiIso（旧 SerrePositivity/DifferentialGraded/Tensor/ProjectiveLeftQuasiIso.lean） -/

/-! # 射影的・semifree右加群を固定した左準同型保存 -/

@[expose] public section ProjectiveLeftQuasiIso
universe u v

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_preserves_leftQuasiIso {M : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : leftModuleQuasiIso A D g) :
    QuasiIso ((BalancedTensor.leftTensorFunctor A D (ForgetEnrichment.to (Complex A) M)).map g) :=
  moduleRelativeKFlat_preserves_leftQuasiIso A D _
    (moduleHomotopicallyProjective_relativeKFlat A D hM) g hg

lemma moduleSemifree_preserves_leftQuasiIso {M : ModuleCategory A D}
    (hM : moduleSemifree A D M) {L L' : LeftModuleCategory A D} (g : L ⟶ L')
    (hg : leftModuleQuasiIso A D g) :
    QuasiIso ((BalancedTensor.leftTensorFunctor A D (ForgetEnrichment.to (Complex A) M)).map g) :=
  moduleRelativeKFlat_preserves_leftQuasiIso A D _ (moduleSemifree_relativeKFlat A D hM) g hg

end SerrePositivity.DifferentialGraded
end

end ProjectiveLeftQuasiIso

/-! ## BimoduleQuasiIso（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleQuasiIso.lean） -/

/-! # bimodule合成の準同型保存に必要な片側の条件

## 概要
bimodule合成の準同型保存に必要な片側の条件。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleTensor.lean、Tensor/
BimoduleKFlatQuasiIso.lean。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleQuasiIso
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

/-- 後の因子の右制限が相対K-flatなら、前の因子の任意の準同型を保存する。 -/
lemma composeMap_first_quasiIso {P P' : BimoduleCategory A B C} (Q : BimoduleCategory A C E)
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (f : P ⟶ P') (hf : BimoduleCategory.quasiIso A B C f) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E f (𝟙 Q)) := by
  intro b e
  rw [composeMap_value_eval]
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id]
  exact moduleRelativeKFlat_preserves_leftQuasiIso A C
    ((BimoduleCategory.underlying A C E Q).rightAt e) (hQ e)
    ((BimoduleCategory.leftEvaluation A B C b).map f)
    (BimoduleCategory.quasiIso_leftEvaluation A B C hf b)

/-- 後の因子の両端の右制限が全Hom射影的なら、前の因子は任意でよい。 -/
lemma composeMap_second_projective_quasiIso (P : BimoduleCategory A B C)
    {Q Q' : BimoduleCategory A C E}
    (hQ : ∀ e, moduleHomotopicallyProjective A C
      ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C
      ((BimoduleCategory.evaluation A C E e).obj Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E (𝟙 P) g) := by
  intro b e
  rw [composeMap_value_eval]
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id]
  exact BalancedTensor.rightTensor_projective_quasiIso A C
    ((BimoduleCategory.underlying A B C P).leftAt b) (hQ e) (hQ' e)
    ((BimoduleCategory.evaluation A C E e).map g)
    (BimoduleCategory.quasiIso_evaluation A C E hg e)

/-- 片側の全Hom射影性で、両変数の準同型を同時に保存する。 -/
lemma composeMap_projective_quasiIso {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E}
    (hQ : ∀ e, moduleHomotopicallyProjective A C
      ((BimoduleCategory.evaluation A C E e).obj Q))
    (hQ' : ∀ e, moduleHomotopicallyProjective A C
      ((BimoduleCategory.evaluation A C E e).obj Q'))
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hf : BimoduleCategory.quasiIso A B C f) (hg : BimoduleCategory.quasiIso A C E g) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E f g) := by
  have h₁ := composeMap_first_quasiIso A B C E Q
    (Bimodule.rightRelativeKFlat_of_rightAt_projective A C E
      (BimoduleCategory.underlying A C E Q) hQ) f hf
  have h₂ := composeMap_second_projective_quasiIso A B C E P' hQ hQ' g hg
  have he := composeMap_comp A B C E f (𝟙 P') (𝟙 Q) g
  simp only [Category.comp_id, Category.id_comp] at he
  rw [he]
  exact (BimoduleCategory.quasiIso A B E).comp_mem _ _ h₁ h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleQuasiIso

/-! ## BimoduleKFlatQuasiIso（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleKFlatQuasiIso.lean） -/

/-! # 右相対K-flat因子間の準同型をbimodule合成が保存する

## 概要
右相対K-flat因子間の準同型をbimodule合成が保存する。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleTensorKFlatComparison.lean。
局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleKFlatQuasiIso
universe u v w z

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [Small.{u} B] [Small.{u} C]

lemma composeMap_second_kFlat_quasiIso (P : BimoduleCategory A B C)
    {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (g : Q ⟶ Q') (hg : BimoduleCategory.quasiIso A C E g) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E (𝟙 P) g) := by
  intro b e
  rw [composeMap_value_eval]
  unfold composeValueMap
  rw [CategoryTheory.Functor.map_id]
  exact BalancedTensor.rightTensor_relativeKFlat_quasiIso A C
    ((BimoduleCategory.underlying A B C P).leftAt b) (hQ e) (hQ' e)
    ((BimoduleCategory.evaluation A C E e).map g)
    (BimoduleCategory.quasiIso_evaluation A C E hg e)

lemma composeMap_kFlat_quasiIso {P P' : BimoduleCategory A B C}
    {Q Q' : BimoduleCategory A C E}
    (hQ : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q))
    (hQ' : Bimodule.rightRelativeKFlat A C E (BimoduleCategory.underlying A C E Q'))
    (f : P ⟶ P') (g : Q ⟶ Q')
    (hf : BimoduleCategory.quasiIso A B C f) (hg : BimoduleCategory.quasiIso A C E g) :
    BimoduleCategory.quasiIso A B E (composeMap A B C E f g) := by
  have h₁ := composeMap_first_quasiIso A B C E Q hQ f hf
  have h₂ := composeMap_second_kFlat_quasiIso A B C E P' hQ hQ' g hg
  have he := composeMap_comp A B C E f (𝟙 P') (𝟙 Q) g
  simp only [Category.comp_id, Category.id_comp] at he
  rw [he]
  exact (BimoduleCategory.quasiIso A B E).comp_mem _ _ h₁ h₂

end SerrePositivity.DifferentialGraded.BimoduleTensor
end

end BimoduleKFlatQuasiIso

/-! ## BimoduleRestrictionKFlat（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleRestrictionKFlat.lean） -/

/-! # 生成cellの右制限からbimodule解像度の右相対K-flat性への帰着

## 概要
生成cellの右制限からbimodule解像度の右相対K-flat性への帰着。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Tensor/BimoduleSemifreeKFlat.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleRestrictionKFlat
universe u v w

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- ここでは生成cellの制限の条件を明示して残す。local Hom条件からの証明は別工程。 -/
lemma rightModuleBimodule_semifree_rightRelativeKFlat
    (hcell : ∀ (c : C) (x : (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (n : ℤ),
      moduleRelativeKFlat A B (ForgetEnrichment.to (Complex A)
        ((tensorRightRestriction A B C c).obj (freeSphere A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ x n))))
    {M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ}
    (hM : moduleSemifree A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ M) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M)) := by
  intro c
  exact moduleRelativeKFlat_of_iso A B (rightModuleBimoduleRightRestrictionIso A B C M c)
    (moduleSemifree_restriction_relativeKFlat A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (tensorRightRestrictionInclusion A B C c) (hcell c) hM)

lemma BimoduleSemifreeResolution.rightRelativeKFlat_of_cells
    {M : BimoduleCategory A B C} (P : BimoduleSemifreeResolution A B C M)
    (hcell : ∀ (c : C) (x : (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (n : ℤ),
      moduleRelativeKFlat A B (ForgetEnrichment.to (Complex A)
        ((tensorRightRestriction A B C c).obj (freeSphere A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ x n)))) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P.obj) :=
  rightModuleBimodule_semifree_rightRelativeKFlat A B C hcell P.semifree

end SerrePositivity.DifferentialGraded
end

end BimoduleRestrictionKFlat

/-! ## BimoduleSemifreeKFlat（旧 SerrePositivity/DifferentialGraded/Tensor/BimoduleSemifreeKFlat.lean） -/

/-! # 相手側local HomのK-flat性から得るsemifree bimodule解像度の右相対K-flat性

## 概要
相手側local HomのK-flat性から得るsemifree bimodule解像度の右相対K-flat性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/KFlatBimoduleResolution.lean。局所導来合成の計算部品、
一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/archive/dg-theory-u12e-general-inventory.mdを参照。
-/

@[expose] public section BimoduleSemifreeKFlat
universe u v w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma restrictedFree_relativeKFlat (hC : localHomKFlat A C) (b₀ : B) (c₀ c : C)
    (K : Complex A) (hK : complexKFlat A K) :
    moduleRelativeKFlat A B (ForgetEnrichment.to (Complex A)
      ((tensorRightRestriction A B C c).obj
        ((freeAt (A := A) (D := (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
          (op ((op b₀, c₀) : DGTensorCategory A Bᵒᵖ C))).obj K))) :=
  moduleRelativeKFlat_of_iso A B (restrictedFreeIso A B C b₀ c₀ c K)
    (freeAt_relativeKFlat A B b₀ (K ⊗ (c₀ ⟶[Complex A] c))
      (complexKFlat_tensor A hK (hC c₀ c)))

lemma restrictedSphere_relativeKFlat (hC : localHomKFlat A C) (c : C)
    (x : (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (n : ℤ) :
    moduleRelativeKFlat A B (ForgetEnrichment.to (Complex A)
      ((tensorRightRestriction A B C c).obj (freeSphere A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ x n))) :=
  restrictedFree_relativeKFlat A B C hC x.unop.1.unop x.unop.2 c
    (complexSphere A n) (complexSphere_kFlat A n)

/-- 相手側Cのlocal Hom条件だけを使う。Bのlocal Hom条件は不要。 -/
lemma BimoduleSemifreeResolution.rightRelativeKFlat
    (hC : localHomKFlat A C) {M : BimoduleCategory A B C}
    (P : BimoduleSemifreeResolution A B C M) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P.obj) :=
  P.rightRelativeKFlat_of_cells A B C (restrictedSphere_relativeKFlat A B C hC)

theorem exists_rightRelativeKFlat_bimodule_resolution (hC : localHomKFlat A C)
    (M : BimoduleCategory A B C) :
    ∃ (P : BimoduleCategory A B C) (q : P ⟶ M),
      Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P) ∧
        BimoduleCategory.quasiIso A B C q := by
  let P := bimoduleCanonicalSemifreeResolution A B C M
  exact ⟨P.obj, P.π, P.rightRelativeKFlat A B C hC, P.quasiIso⟩

end SerrePositivity.DifferentialGraded
end

end BimoduleSemifreeKFlat

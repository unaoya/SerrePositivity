module

public import SerrePositivity.BhattScholze.Andre.Transfinite.AlgebraCategory
open SerrePositivity SerrePositivity.BhattScholze.Andre.Transfinite
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
variable (step : ∀ (B : Type u) [CommRing B] (_hB : IsIntegralPerfectoid B p)
    {σ : Type u} (f : σ → Polynomial B), (∀ s, (f s).Monic ∧ 0 < (f s).natDegree) →
    ∃ (T : Type u) (_ : CommRing T) (φ : B →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0)
include step in
/-- ## 概要
固定初段上の塔の代数には、全正次数モニック多項式の根を含む後続対象への射が存在する。
BS Thm 7.14（著者版 p.61）の超限反復。

## 方針
すべての正次数モニック多項式の部分型を添字とする族に指定 step を適用し、
初段からの完全忠実平坦性を元の係数射との合成で保持する。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
theorem exists_root_successor (X : AndreTowerAlgebra R p) :
    ∃ (Y : AndreTowerAlgebra R p) (φ : X ⟶ Y),
      ∀ (P : Polynomial X), P.Monic → 0 < P.natDegree →
        ∃ y : Y, P.eval₂ φ.toRingHom y = 0 := by
  let σ := {P : Polynomial X // P.Monic ∧ 0 < P.natDegree}
  obtain ⟨T, hTinst, φ, ρ, hT, hφ, hroot⟩ :=
    step X X.perfectoid (fun P : σ ↦ P.val) (fun P ↦ P.property)
  let := hTinst
  let β := φ.comp X.baseMap
  have hβ : letI := β.toAlgebra;
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T :=
    isCompletelyFaithfullyFlat_natCast_comp X.baseMap φ p X.flat hφ
  let Y : AndreTowerAlgebra R p := ⟨T, β, hT, hβ⟩
  refine ⟨Y, ⟨φ, rfl⟩, ?_⟩
  intro P hP hdeg
  exact ⟨ρ ⟨P, hP, hdeg⟩, hroot ⟨P, hP, hdeg⟩⟩

/-- ## 概要
任意の可換環 R は、自身上で任意のイデアル I に関して完全忠実平坦である。
BS Thm 7.14（著者版 p.61）の超限反復。

## 方針
R の平坦性から正次数 Tor を消し、剰余テンソルを剰余環自身と線形同型で比較する。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
theorem isCompletelyFaithfullyFlat_self (I : Ideal R) : IsCompletelyFaithfullyFlat I R := by
  constructor
  · intro N _ _ hN
    apply (isConcentratedInDegreeZero_derivedTensor_iff R N).mpr
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact torModule_subsingleton_of_flat R N m
  · exact Module.FaithfullyFlat.of_linearEquiv (R ⧸ I) (R ⧸ I)
      (TensorProduct.AlgebraTensorModule.rid R (R ⧸ I) (R ⧸ I))

/-- ## 概要
指定 step の存在証明から、塔の代数の後続対象を選ぶ。
BS Thm 7.14（著者版 p.61）の超限反復。

## 方針
証明済みの後続対象の存在に Classical.choose を適用する。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
def rootSuccessor (X : AndreTowerAlgebra R p) : AndreTowerAlgebra R p :=
  (exists_root_successor R p step X).choose
/-- ## 概要
選んだ後続対象への、固定初段と両立する環射を選ぶ。
BS Thm 7.14（著者版 p.61）の超限反復。

## 方針
同じ後続存在証明から射を取り出す。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
def rootSuccessorMap (X : AndreTowerAlgebra R p) : X ⟶ rootSuccessor R p step X :=
  (exists_root_successor R p step X).choose_spec.choose
/-- ## 概要
選んだ後続対象は、前段の全正次数モニック多項式の根を持つ。
BS Thm 7.14（著者版 p.61）の超限反復。

## 方針
後続存在証明の同じ選択に付随する根の存在条件を取り出す。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
theorem rootSuccessorMap_roots (X : AndreTowerAlgebra R p) (P : Polynomial X)
    (hP : P.Monic) (hdeg : 0 < P.natDegree) :
    ∃ y : rootSuccessor R p step X,
      P.eval₂ (rootSuccessorMap R p step X).toRingHom y = 0 :=
  (exists_root_successor R p step X).choose_spec.choose_spec P hP hdeg

/-- ## 概要
perfectoid な初段 R と指定 step から、Mathlib の超限反復用の後続操作を作る。
BS Thm 7.14（著者版 p.61）の超限反復。

## 方針
零段は R 自身と恒等係数射とし、後続対象と射は一段拡大の選択を使う。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
def rootSuccessorStructure (hR : IsIntegralPerfectoid R p) :
    SuccStruct (AndreTowerAlgebra R p) where
  X₀ := ⟨R, RingHom.id R, hR, isCompletelyFaithfullyFlat_self R (Ideal.span {(p : R)})⟩
  succ := rootSuccessor R p step
  toSucc := rootSuccessorMap R p step


/-- ## 概要
非空整列線形順序に沿う超限反復に必要な、塔の代数の圏の余極限条件が成り立つ。
BS Thm 7.14（著者版 p.61）の超限反復。

## 方針
全体と各真の極限初期区間に、検証済みの整列添字余極限を供給する。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
instance andreTowerAlgebra_hasIterationOfShape {J : Type u}
    [LinearOrder J] [Nonempty J] [WellFoundedLT J] :
    HasIterationOfShape J (AndreTowerAlgebra R p) where
  hasColimitsOfShape := inferInstance
  hasColimitsOfShape_of_isSuccLimit j hj := by
    let := hj.nonempty_Iio.to_subtype
    infer_instance

open Ordinal Cardinal in
/-- ## 概要
perfectoid 環 R には、perfectoid かつ絶対整閉な環 S への p 完全忠実平坦な代数構造が存在する。
ただし、正次数条件を追加した指定の一段拡大 step を明示仮定とする。
BS Thm 7.14（著者版 p.61）の超限反復。

## 方針
固定初段上の perfectoid・p 完全忠実平坦代数の圏で、全正次数モニックの根を添加する操作を
ω₁ まで反復する。真の極限段は環余極限の p 進完備化で構成する。終段には未完備余極限を使い、
可算データの降下でその自動的完備性を証明する。有限個の多項式係数が一段に入り、次段の根を
終段へ写すことで絶対整閉性を得る。

## 規約
基底環・各段・終段と添字は Type u に留める。後続操作は正次数条件付きの指定 step を使う。
元の初段の係数射に関する完全忠実平坦性を保持する。

## 使われ方
一段拡大の成果を step に入力し、同じ宇宙の André 拡大の存在結論を得る。
-/
theorem exists_completelyFaithfullyFlat_absolutelyIntegrallyClosed
    (hR : IsIntegralPerfectoid R p)
    (step : ∀ (B : Type u) [CommRing B] (_hB : IsIntegralPerfectoid B p)
    {σ : Type u} (f : σ → Polynomial B), (∀ s, (f s).Monic ∧ 0 < (f s).natDegree) →
    ∃ (T : Type u) (_ : CommRing T) (φ : B →+* T) (ρ : σ → T),
      IsIntegralPerfectoid T p ∧
      (letI := φ.toAlgebra; IsCompletelyFaithfullyFlat (Ideal.span {(p : B)}) T) ∧
      ∀ s, (f s).eval₂ φ (ρ s) = 0) :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S),
      IsIntegralPerfectoid S p ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) S ∧
      IsAbsolutelyIntegrallyClosed S := by
  let J := Ordinal.ToType (ω₁ : Ordinal.{u})
  let Φ := rootSuccessorStructure R p step hR
  let F := Φ.iterationFunctor J
  let A := AndreTowerAlgebra.diagramRing F
  let f := AndreTowerAlgebra.diagramMap F
  let L := Ring.DirectLimit A (fun i j h ↦ (f i j h).toRingHom)
  let := algebraRingDirectLimitAlgebra A f
  have hperf : IsIntegralPerfectoid L p :=
    isIntegralPerfectoid_ringDirectLimit_of_countable_upperBound_without_flatness A
      (fun i j h ↦ (f i j h).toRingHom) omegaOneIndex_countable_upperBound p
      (fun i ↦ (F.obj i).perfectoid)
  have hflat : IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) L :=
    isCompletelyFaithfullyFlat_algebraRingDirectLimit A f _ (fun i ↦ (F.obj i).flat)
  refine ⟨L, inferInstance, inferInstance, hperf, hflat, ?_⟩
  apply isAbsolutelyIntegrallyClosed_directLimit_of_eventual_roots A
    (fun i j h ↦ (f i j h).toRingHom)
  intro i P hP hdeg
  obtain ⟨y, hy⟩ := rootSuccessorMap_roots R p step (F.obj i) P hP hdeg
  let e := Φ.iterationFunctorObjSuccIso i (not_isMax i)
  refine ⟨Order.succ i, Order.le_succ i, e.inv.toRingHom y, ?_⟩
  have he : F.map (homOfLE (Order.le_succ i)) =
      rootSuccessorMap R p step (F.obj i) ≫ e.inv :=
    Φ.iterationFunctor_map_succ i (not_isMax i)
  change P.eval₂ ((F.map (homOfLE (Order.le_succ i))).toRingHom) (e.inv.toRingHom y) = 0
  rw [he]
  change P.eval₂ (e.inv.toRingHom.comp (rootSuccessorMap R p step (F.obj i)).toRingHom)
    (e.inv.toRingHom y) = 0
  rw [← Polynomial.hom_eval₂, hy, map_zero]
end SerrePositivity.BhattScholze.Andre.Transfinite

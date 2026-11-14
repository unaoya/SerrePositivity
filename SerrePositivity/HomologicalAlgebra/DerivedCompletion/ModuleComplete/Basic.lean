module


public meta import SerrePositivity.Util.Citation
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # 主イデアルに関する導来完備性

## 概要

標準の導来圏で `R[1/f][0]` から全ての整数次数の shifted Hom が消えることを導来 `f` 完備性 `IsComplete` と定め（Stacks 091N の全次数の Ext の消滅条件）、加群を零次に置いた対象の完備性 `IsModuleComplete` を定める。`f` の冪で零化されれば完備であることを示す。

## 方針

ホモトピー逆極限との同値や通常のイデアル進完備性との同値はここでは使わない。

## 規約

`IsModuleComplete` は BhattScholze・CLMST が多く使うので名前を変えない。旧 `Basic`・`Module`。出典：https://stacks.math.columbia.edu/tag/091N。

## 使われ方

DerivedCompletion の全体、BhattScholze、CLMST。
-/

@[expose] public noncomputable section

universe u

section BasicPart

namespace SerrePositivity.DerivedCompletion

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- 加群の cochain 複体を擬同型で局所化して構成した標準的な導来圏。
導来圏の存在を追加仮定とせず、Mathlib の実際の局所化を固定する。 -/
abbrev ConcreteDerivedCategory := DerivedCategory (ModuleCat.{u} R)

/-- 加群を零次数に置いて標準的な実導来圏へ移す関手。 -/
def moduleObjectFunctor : ModuleCat.{u} R ⥤ ConcreteDerivedCategory R :=
  DerivedCategory.singleFunctor (ModuleCat.{u} R) 0

instance : (moduleObjectFunctor R).Linear R := by
  dsimp [moduleObjectFunctor]
  infer_instance

instance : (moduleObjectFunctor R).Additive := by
  dsimp [moduleObjectFunctor]
  infer_instance

/-- 主元 `f` を反転した標準局所化を、元の環上の加群として零次数に置いた導来対象。 -/
def localizationObject (f : R) : ConcreteDerivedCategory R :=
  (moduleObjectFunctor R).obj (ModuleCat.of R (Localization.Away f))

/-- 導来 `f` 完備性：標準局所化 `R[1/f][0]` から対象への全整数次数の射が零。
これは Ext の全次数の消滅を直接記述する条件であり、逆極限に関する条件へ置き換えていない。 -/
def IsComplete (f : R) (K : ConcreteDerivedCategory R) : Prop :=
  ∀ n : ℤ, ∀ a : ShiftedHom (localizationObject R f) K n, a = 0

variable {R}

/-- 線形圏で、始域のスカラー倍が同型、終域の同じスカラー倍が零なら、すべての射は零。
スカラー倍の自然性と、始域側の同型の右消去を使う。 -/
theorem hom_eq_zero_of_scalar_zero {C : Type*} [Category* C] [Preadditive C] [Linear R C]
    (r : R) {X Y : C} [IsIso (r • 𝟙 X)] (hY : r • 𝟙 Y = 0) (a : X ⟶ Y) :
    a = 0 := by
  apply (cancel_epi (r • 𝟙 X)).mp
  have h : a ≫ (r • 𝟙 Y) = 0 := by rw [hY, comp_zero]
  simpa using h

/-- `f` の任意の冪は、局所化加群の上で同型として作用する。
局所化における `f` の単元性から加群のスカラー倍の全単射性を得る。 -/
theorem localizationModule_scalar_isIso (f : R) (N : ℕ) :
    IsIso ((f ^ N) • 𝟙 (ModuleCat.of R (Localization.Away f))) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (fun m : Localization.Away f => (f ^ N) • m)
  simp only [Algebra.smul_def, map_pow]
  exact IsUnit.isUnit_iff_mulLeft_bijective.mp
    (IsLocalization.Away.algebraMap_pow_isUnit (S := Localization.Away f) f N)

variable (R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- 局所化導来対象の上でも `f` の任意の冪の作用は同型。
零次数の導来関手が同型とスカラー倍を保つことを使う。 -/
theorem localizationObject_scalar_isIso (f : R) (N : ℕ) :
    IsIso ((f ^ N) • 𝟙 (localizationObject R f)) := by
  have := localizationModule_scalar_isIso f N
  have h := Functor.map_isIso (moduleObjectFunctor R)
    ((f ^ N) • 𝟙 (ModuleCat.of R (Localization.Away f)))
  change IsIso ((f ^ N) • 𝟙 ((moduleObjectFunctor R).obj
    (ModuleCat.of R (Localization.Away f))))
  rw [Functor.map_smul, (moduleObjectFunctor R).map_id] at h
  exact h

/-- 導来圏で `f` のある冪の作用が零なら、対象は導来 `f` 完備。
シフトがスカラー倍を保ち、局所化始域上の同じ冪の作用は同型なので、全次数の射が消える。 -/
theorem isComplete_of_scalar_pow_zero (f : R) (K : ConcreteDerivedCategory R)
    (N : ℕ) (hK : (f ^ N) • 𝟙 K = 0) : IsComplete R f K := by
  intro n a
  have := localizationObject_scalar_isIso R f N
  have hn : (f ^ N) • 𝟙 (K⟦n⟧) = 0 := by
    have h := congrArg ((shiftFunctor (ConcreteDerivedCategory R) n).map) hK
    simpa using h
  exact hom_eq_zero_of_scalar_zero (f ^ N) hn a

/-- `f` の冪の作用が零ホモトピックな複体の導来像は、導来 `f` 完備。
作用が鎖写像として厳密に零であることは要求せず、導来局所化での零性を使う。 -/
theorem isComplete_Q_of_scalar_pow_nullHomotopic (f : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (N : ℕ)
    (hK : Homotopy ((f ^ N) • 𝟙 K) 0) :
    IsComplete R f (DerivedCategory.Q.obj K) := by
  apply isComplete_of_scalar_pow_zero R f _ N
  have h := DerivedCategory.Q_map_eq_of_homotopy (ModuleCat.{u} R) hK
  simpa using h

end SerrePositivity.DerivedCompletion

end BasicPart

section ModulePart

namespace SerrePositivity.DerivedCompletion

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

variable (R : Type u) [CommRing R]

/-- 加群の導来 `f` 完備性：零次数に置いた加群が、局所化からの全次数の射の消滅を満たす。 -/
def IsModuleComplete (f : R) (M : ModuleCat.{u} R) : Prop :=
  IsComplete R f ((moduleObjectFunctor R).obj M)

/-- `f` のある冪が加群のすべての元を零化すれば、加群は導来 `f` 完備。
加群上の零化を自己射の零性へ移し、零次数の導来関手で導来圏の零化を得る。 -/
theorem isModuleComplete_of_pow_smul_zero (f : R) (M : ModuleCat.{u} R) (N : ℕ)
    (hM : ∀ m : M, (f ^ N) • m = 0) : IsModuleComplete R f M := by
  have hzero : (f ^ N) • 𝟙 M = 0 := by
    ext m
    exact hM m
  apply isComplete_of_scalar_pow_zero R f _ N
  have h := congrArg ((moduleObjectFunctor R).map) hzero
  simpa using h

/-- 自然数 `p` の冪で零化される加群は、環に写した `p` に関して導来完備。
素数性の仮定は不要であり、通常の `p` 冪 torsion 加群を直接扱える。 -/
theorem isModuleComplete_of_natCast_pow_smul_zero (p N : ℕ) (M : ModuleCat.{u} R)
    (hM : ∀ m : M, ((p : R) ^ N) • m = 0) :
    IsModuleComplete R (p : R) M :=
  isModuleComplete_of_pow_smul_zero R (p : R) M N hM

/-- イデアルが `f` の冪を含めば、その商環を基底環の加群とみたものは導来 `f` 完備。
商環への像が零であることから加群の零化条件を得る。 -/
theorem isModuleComplete_quotient_of_pow_mem (f : R) (I : Ideal R) (N : ℕ)
    (hN : f ^ N ∈ I) : IsModuleComplete R f (ModuleCat.of R (R ⧸ I)) := by
  apply isModuleComplete_of_pow_smul_zero R f _ N
  intro m
  have hzero : algebraMap R (R ⧸ I) (f ^ N) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hN
  change algebraMap R (R ⧸ I) (f ^ N) * m = 0
  rw [hzero, zero_mul]

/-- `f` の冪で生成される主イデアルによる商環は、導来 `f` 完備。
特に自然数 `p` の環への像を代入して `R/(p^N)` に適用できる。 -/
theorem isModuleComplete_quotient_span_pow (f : R) (N : ℕ) :
    IsModuleComplete R f (ModuleCat.of R (R ⧸ Ideal.span {f ^ N})) := by
  apply isModuleComplete_quotient_of_pow_mem R f _ N
  exact Ideal.subset_span (Set.mem_singleton _)

end SerrePositivity.DerivedCompletion

end ModulePart

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.3.22" (partial := component) "仮定：通常の可換環 R と一元 a、通常の導来対象（Lean が強い：主元による局所化 R[1/a] の検査の場合）。結論：R[1/a][0] から全整数シフトの射が零となることを導来完備性として定義する（S-local な検査対象のこの部分に一致）。任意の全 S-local 対象への直交との同値はこの定義に含まれない。"] _root_.SerrePositivity.DerivedCompletion.IsComplete

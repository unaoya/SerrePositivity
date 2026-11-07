module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.CupLeibniz
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Alexander–Whitney 積のコホモロジーへの降下

## 概要
余鎖の積を余輪体の積に制限し、余境界で割ってコホモロジーの積を得る。

## 方針
Leibniz 則から余輪体との積は余境界を保つことを示し、Mathlib の短複体の商表示を使う。

## 規約
余鎖次数は自然数で、次数 0 の余境界は零。

## 使われ方
Hodge–Tate 写像の積と Bockstein の Leibniz 則。
-/

public section
noncomputable section

universe u

open CategoryTheory
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

variable (X : CosimplicialObject CommRingCat.{u})

/-- 余単体的可換環の台加法群の交代余面複体。 -/
abbrev ringCochainComplex : CochainComplex AddCommGrpCat.{u} ℕ :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).obj
    (X ⋙ forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)

/-- 余鎖複体の指定次数を中心とする短複体。 -/
abbrev ringCochainShortComplex (n : ℕ) :=
  (ringCochainComplex X).sc' (n - 1) n (n + 1)

/-- 交代余面複体の次の次数への微分は余鎖微分。 -/
theorem ringCochainComplex_d_apply (n : ℕ) (x : X.obj ⦋n⦌) :
    (ringCochainComplex X).d n (n + 1) x = cochainDifferential X n x := by
  dsimp only [ringCochainComplex, AlgebraicTopology.alternatingCofaceMapComplex,
    AlgebraicTopology.AlternatingCofaceMapComplex.obj, CochainComplex.of]
  rw [CochainComplex.of_d]
  rfl

private theorem outgoing_apply (n : ℕ) (x : X.obj ⦋n⦌) :
    (ringCochainShortComplex X n).g x = cochainDifferential X n x :=
  ringCochainComplex_d_apply X n x

/-- 交代余面複体の余輪体の加法群。 -/
abbrev Cocycles (n : ℕ) := (ringCochainShortComplex X n).g.hom.ker

private theorem cast_zero {i j : ℕ} (h : i = j) :
    cast (congrArg (fun n => (X.obj ⦋n⦌ : Type u)) h) (0 : X.obj ⦋i⦌) = 0 := by
  subst j
  rfl

/-- 余輪体の cup 積。 -/
@[expose]
def cocycleCup {m n : ℕ} (a : Cocycles X m) (b : Cocycles X n) :
    Cocycles X (m + n) :=
  ⟨cup X a.1 b.1, by
    change (ringCochainShortComplex X (m + n)).g (cup X a.1 b.1) = 0
    have ha : cochainDifferential X m a.1 = 0 := (outgoing_apply X m a.1).symm.trans a.2
    have hb : cochainDifferential X n b.1 = 0 := (outgoing_apply X n b.1).symm.trans b.2
    erw [outgoing_apply, cochainDifferential_cup, ha, hb]
    have hleft : cup X (0 : X.obj ⦋m + 1⦌) b.1 = 0 := by simp [cup]
    have hright : cup X a.1 (0 : X.obj ⦋n + 1⦌) = 0 := by simp [cup]
    erw [hleft, hright, smul_zero, add_zero]
    exact cast_zero X (by omega : (m + 1) + n = m + n + 1)⟩

private theorem cocycleCup_add_left {m n : ℕ} (a a' : Cocycles X m) (b : Cocycles X n) :
    cocycleCup X (a + a') b = cocycleCup X a b + cocycleCup X a' b :=
  Subtype.ext (add_cup X a.1 a'.1 b.1)

private theorem cocycleCup_add_right {m n : ℕ} (a : Cocycles X m) (b b' : Cocycles X n) :
    cocycleCup X a (b + b') = cocycleCup X a b + cocycleCup X a b' :=
  Subtype.ext (cup_add X a.1 b.1 b'.1)

private abbrev boundaries (n : ℕ) := (ringCochainShortComplex X n).abToCycles.range

private theorem isBoundary_iff {i j : ℕ} (h : i + 1 = j) (z : Cocycles X j) :
    z ∈ boundaries X j ↔ ∃ a : X.obj ⦋i⦌,
      cast (congrArg (fun n => (X.obj ⦋n⦌ : Type u)) h) (cochainDifferential X i a) = z.1 := by
  subst j
  change (∃ a : (ringCochainShortComplex X (i + 1)).X₁,
    (ringCochainShortComplex X (i + 1)).abToCycles a = z) ↔ _
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (ringCochainComplex_d_apply X i a).symm.trans (congrArg Subtype.val ha)⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ((ringCochainComplex_d_apply X i a).trans ha)⟩

private theorem boundary_zero {z : Cocycles X 0} (hz : z ∈ boundaries X 0) : z = 0 := by
  obtain ⟨a, ha⟩ := hz
  have h := congrArg Subtype.val ha
  change (ringCochainComplex X).d 0 0 a = z.1 at h
  rw [HomologicalComplex.shape _ _ _ (by simp)] at h
  exact Subtype.ext h.symm

private theorem cocycleCup_zero_left {m n : ℕ} (b : Cocycles X n) :
    cocycleCup X (0 : Cocycles X m) b = 0 := by
  apply Subtype.ext
  change cup X (0 : X.obj ⦋m⦌) b.1 = 0
  simp [cup]

private theorem cocycleCup_zero_right {m n : ℕ} (a : Cocycles X m) :
    cocycleCup X a (0 : Cocycles X n) = 0 := by
  apply Subtype.ext
  change cup X a.1 (0 : X.obj ⦋n⦌) = 0
  simp [cup]

private theorem boundary_cup_left {m n : ℕ} (a : Cocycles X m) (b : Cocycles X n)
    (ha : a ∈ boundaries X m) : cocycleCup X a b ∈ boundaries X (m + n) := by
  cases m with
  | zero =>
    rw [boundary_zero X ha, cocycleCup_zero_left]
    exact (boundaries X (0 + n)).zero_mem
  | succ m =>
    obtain ⟨x, hx⟩ := (isBoundary_iff X (i := m) rfl a).mp ha
    change cochainDifferential X m x = a.1 at hx
    have hb : cochainDifferential X n b.1 = 0 := (outgoing_apply X n b.1).symm.trans b.2
    have h := cochainDifferential_cup X x b.1
    erw [hx, hb] at h
    have hzero : cup X x (0 : X.obj ⦋n + 1⦌) = 0 := by simp [cup]
    rw [hzero, smul_zero, add_zero] at h
    refine (isBoundary_iff X (by omega : m + n + 1 = m.succ + n) _).mpr
      ⟨cup X x b.1, ?_⟩
    rw [h, cast_cast]
    rfl

private theorem boundary_cup_right {m n : ℕ} (a : Cocycles X m) (b : Cocycles X n)
    (hb : b ∈ boundaries X n) : cocycleCup X a b ∈ boundaries X (m + n) := by
  cases n with
  | zero =>
    rw [boundary_zero X hb, cocycleCup_zero_right]
    exact (boundaries X (m + 0)).zero_mem
  | succ n =>
    obtain ⟨y, hy⟩ := (isBoundary_iff X (i := n) rfl b).mp hb
    change cochainDifferential X n y = b.1 at hy
    have ha : cochainDifferential X m a.1 = 0 := (outgoing_apply X m a.1).symm.trans a.2
    have h := cochainDifferential_cup X a.1 y
    erw [ha, hy] at h
    have hzero : cup X (0 : X.obj ⦋m + 1⦌) y = 0 := by simp [cup]
    rw [hzero, cast_zero X (by omega : (m + 1) + n = m + n + 1), zero_add] at h
    refine (isBoundary_iff X (by omega : m + n + 1 = m + n.succ) _).mpr
      ⟨(-1 : ℤ) ^ m • cup X a.1 y, ?_⟩
    change cochainDifferential X (m + n) ((-1 : ℤ) ^ m • cup X a.1 y) = cup X a.1 b.1
    rw [map_zsmul, h, smul_smul, ← mul_pow]
    simp

private abbrev CohomologyQuotient (n : ℕ) := Cocycles X n ⧸ boundaries X n

private def quotientCupLeft {m n : ℕ} (b : Cocycles X n) :
    CohomologyQuotient X m →+ CohomologyQuotient X (m + n) :=
  QuotientAddGroup.lift _ ((QuotientAddGroup.mk' _).comp
    { toFun := fun a => cocycleCup X a b
      map_zero' := cocycleCup_zero_left X b
      map_add' := fun a a' => cocycleCup_add_left X a a' b }) (by
    intro a ha
    change QuotientAddGroup.mk (cocycleCup X a b) = 0
    exact (QuotientAddGroup.eq_zero_iff _).mpr (boundary_cup_left X a b ha))

private theorem quotientCupLeft_mk {m n : ℕ} (a : Cocycles X m) (b : Cocycles X n) :
    quotientCupLeft X b (QuotientAddGroup.mk a) = QuotientAddGroup.mk (cocycleCup X a b) :=
  rfl

private def quotientCup {m n : ℕ} (a : CohomologyQuotient X m) :
    CohomologyQuotient X n →+ CohomologyQuotient X (m + n) :=
  QuotientAddGroup.lift _
    { toFun := fun b => quotientCupLeft X b a
      map_zero' := by
        induction a using QuotientAddGroup.induction_on with
        | H a =>
          rw [quotientCupLeft_mk, cocycleCup_zero_right]
          rfl
      map_add' := by
        intro b b'
        induction a using QuotientAddGroup.induction_on with
        | H a =>
          simp only [quotientCupLeft_mk, cocycleCup_add_right, QuotientAddGroup.mk_add] } (by
    intro b hb
    induction a using QuotientAddGroup.induction_on with
    | H a =>
      change quotientCupLeft X b (QuotientAddGroup.mk a) = 0
      rw [quotientCupLeft_mk, QuotientAddGroup.eq_zero_iff]
      exact boundary_cup_right X a b hb)

private theorem prev_eq_sub_one (n : ℕ) : (ComplexShape.up ℕ).prev n = n - 1 := by
  cases n with
  | zero => exact CochainComplex.prev_nat_zero
  | succ n => exact CochainComplex.prev_nat_succ n

private def cohomologyQuotientIso (n : ℕ) :
    (ringCochainComplex X).homology n ≅ AddCommGrpCat.of (CohomologyQuotient X n) :=
  (ringCochainComplex X).homologyIsoSc' (n - 1) n (n + 1) (prev_eq_sub_one n)
    (CochainComplex.next ℕ n) ≪≫ (ringCochainShortComplex X n).abHomologyIso

/-- 概要：余単体的可換環のコホモロジー上の cup 積。
方針：両変数で余輪体と余境界を保つことから、商に降ろす。
規約：Alexander–Whitney 積の順序と符号を引き継ぐ。
使われ方：Hodge–Tate 比較に現れるコホモロジー環。 -/
def cohomologyCup {m n : ℕ} (a : cohomology X m) (b : cohomology X n) :
    cohomology X (m + n) :=
  (cohomologyQuotientIso X (m + n)).inv
    (quotientCup X ((cohomologyQuotientIso X m).hom a) ((cohomologyQuotientIso X n).hom b))

/-- 余輪体からコホモロジー類への標準写像。 -/
def cohomologyClass (n : ℕ) : Cocycles X n →+ cohomology X n :=
  (cohomologyQuotientIso X n).inv.hom.comp (QuotientAddGroup.mk' _)

/-- 各コホモロジー類は余輪体で表される。 -/
theorem cohomologyClass_surjective (n : ℕ) : Function.Surjective (cohomologyClass X n) := by
  intro x
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective ((cohomologyQuotientIso X n).hom x)
  exact ⟨a, by simp [cohomologyClass, ha, ← ConcreteCategory.comp_apply]⟩

/-- コホモロジーの cup 積は余輪体の cup 積の類。 -/
@[simp]
theorem cohomologyCup_class {m n : ℕ} (a : Cocycles X m) (b : Cocycles X n) :
    cohomologyCup X (cohomologyClass X m a) (cohomologyClass X n b) =
      cohomologyClass X (m + n) (cocycleCup X a b) := by
  simp only [cohomologyCup, cohomologyClass, AddMonoidHom.comp_apply]
  change (cohomologyQuotientIso X (m + n)).inv
    (quotientCup X
      ((cohomologyQuotientIso X m).hom ((cohomologyQuotientIso X m).inv (QuotientAddGroup.mk a)))
      ((cohomologyQuotientIso X n).hom ((cohomologyQuotientIso X n).inv (QuotientAddGroup.mk b)))) = _
  simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply]
  rfl

/-- 余輪体の部分群から、複体の圏論的な核への標準写像。 -/
def cycleRepresentative (n : ℕ) :
    AddCommGrpCat.of (Cocycles X n) ⟶ (ringCochainComplex X).cycles n :=
  (ringCochainShortComplex X n).abCyclesIso.inv ≫
    ((ringCochainComplex X).cyclesIsoSc' (n - 1) n (n + 1)
      (prev_eq_sub_one n) (CochainComplex.next ℕ n)).inv

/-- 核への標準写像は台の余鎖を保つ。 -/
theorem cycleRepresentative_apply (n : ℕ) (a : Cocycles X n) :
    (ringCochainComplex X).iCycles n (cycleRepresentative X n a) = a.1 := by
  rw [← ConcreteCategory.comp_apply, cycleRepresentative, Category.assoc,
    HomologicalComplex.cyclesIsoSc'_inv_iCycles, ConcreteCategory.comp_apply]
  exact (ringCochainShortComplex X n).abCyclesIso_inv_apply_iCycles a

/-- コホモロジー類の写像は複体のホモロジーへの標準射で計算できる。 -/
theorem cohomologyClass_apply (n : ℕ) (a : Cocycles X n) :
    cohomologyClass X n a = (ringCochainComplex X).homologyπ n (cycleRepresentative X n a) := by
  change ((cohomologyQuotientIso X n).inv ∘
    AddCommGrpCat.ofHom (QuotientAddGroup.mk' _)) a = _
  simp only [Function.comp_apply, ← ConcreteCategory.comp_apply, cohomologyQuotientIso,
    Iso.trans_inv, cycleRepresentative]
  congr 1
  rw [Category.assoc ((ringCochainShortComplex X n).abCyclesIso.inv),
    ← HomologicalComplex.π_homologyIsoSc'_inv, ← Category.assoc]
  congr 1

private abbrev ringCochainMap (Y : CosimplicialObject CommRingCat.{u}) (f : X ⟶ Y) :
    ringCochainComplex X ⟶ ringCochainComplex Y :=
  (AlgebraicTopology.alternatingCofaceMapComplex _).map
    (Functor.whiskerRight f (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))

/-- 余単体的環の射が余輪体に誘導する加法準同型。 -/
@[expose]
def cocycleMap (Y : CosimplicialObject CommRingCat.{u}) (f : X ⟶ Y) (n : ℕ) :
    Cocycles X n →+ Cocycles Y n :=
  AddMonoidHom.mk' (fun a => ⟨f.app ⦋n⦌ a.1, by
    change (ringCochainComplex Y).d n (n + 1) ((ringCochainMap X Y f).f n a.1) = 0
    rw [← ConcreteCategory.comp_apply, (ringCochainMap X Y f).comm,
      ConcreteCategory.comp_apply]
    have ha : (ringCochainComplex X).d n (n + 1) a.1 = 0 := a.2
    rw [ha, map_zero]⟩) (fun a b => by
      apply Subtype.ext
      change f.app ⦋n⦌ (a.1 + b.1 : X.obj ⦋n⦌) = f.app ⦋n⦌ a.1 + f.app ⦋n⦌ b.1
      exact map_add (f.app ⦋n⦌).hom (a.1 : X.obj ⦋n⦌) (b.1 : X.obj ⦋n⦌))

private theorem cycleRepresentative_natural (Y : CosimplicialObject CommRingCat.{u})
    (f : X ⟶ Y) (n : ℕ) (a : Cocycles X n) :
    HomologicalComplex.cyclesMap (ringCochainMap X Y f) n (cycleRepresentative X n a) =
      cycleRepresentative Y n (cocycleMap X Y f n a) := by
  apply (AddCommGrpCat.mono_iff_injective ((ringCochainComplex Y).iCycles n)).mp inferInstance
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
    ConcreteCategory.comp_apply, cycleRepresentative_apply, cycleRepresentative_apply]
  rfl

/-- コホモロジーに誘導される写像は余輪体の像で計算できる。 -/
@[simp]
theorem cohomologyMap_class (Y : CosimplicialObject CommRingCat.{u})
    (f : X ⟶ Y) (n : ℕ) (a : Cocycles X n) :
    cohomologyMap X Y f n (cohomologyClass X n a) =
      cohomologyClass Y n (cocycleMap X Y f n a) := by
  rw [cohomologyClass_apply, cohomologyClass_apply]
  change HomologicalComplex.homologyMap (ringCochainMap X Y f) n
    ((ringCochainComplex X).homologyπ n (cycleRepresentative X n a)) = _
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply, cycleRepresentative_natural]

/-- 概要：余単体的環の射がコホモロジーの cup 積を保つ。
方針：余輪体で代表し、余鎖の cup 積の自然性を使う。
規約：Alexander–Whitney 積。
使われ方：Čech–Alexander 模型間の比較。 -/
theorem cohomologyMap_cup (Y : CosimplicialObject CommRingCat.{u})
    (f : X ⟶ Y) {m n : ℕ} (a : cohomology X m) (b : cohomology X n) :
    cohomologyMap X Y f (m + n) (cohomologyCup X a b) =
      cohomologyCup Y (cohomologyMap X Y f m a) (cohomologyMap X Y f n b) := by
  obtain ⟨a, rfl⟩ := cohomologyClass_surjective X m a
  obtain ⟨b, rfl⟩ := cohomologyClass_surjective X n b
  simp only [cohomologyCup_class, cohomologyMap_class]
  congr 1
  apply Subtype.ext
  exact cup_natural X f a.1 b.1

end SerrePositivity.Cosimplicial

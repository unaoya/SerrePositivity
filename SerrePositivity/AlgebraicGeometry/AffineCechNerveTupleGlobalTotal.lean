module

public import SerrePositivity.AlgebraicGeometry.AffineCechNerveTupleQuasiIso
public import SerrePositivity.AlgebraicGeometry.CechIntegerLiftTotalMonoQuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
概要：同じアフィンnerveの大域増大を、同じ全複体の擬同型へ渡す。
方針：singleの各成分の単射性と既存の各列の擬同型を使う。
規約：実際のΓの係数写像とタプル被覆の自然変換を保つČech版。
使われ方：元の環のconerveとタプルの二重Čechの比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial
universe u
local notation "up" => ComplexShape.up ℕ
variable {Y S : Scheme.{u}} (f : Y ⟶ S) [IsAffine Y] [IsAffine S]
variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime)
variable (h : ∀ n : SimplexCategoryᵒᵖ,
  ∀ O, (p : ((Arrow.mk f).cechNerve.obj n).presheaf.obj O) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じアフィンnerveのsingleからの実際の増大は、全成分で単射。 -/
theorem affineCechNerveTupleGlobalAugmentation_mono_f
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) (n : SimplexCategory) (b : ℕ) :
    Mono ((schemePerfectCechTupleGlobalAugmentationHom f U p hp h n).f b) := by
  cases b with
  | zero =>
    rw [schemePerfectCechTupleGlobalAugmentationHom_f_zero]
    letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
    let ε := ModuleCat.ofHom (schemeStructurePerfectCechAugmentation
      ((Arrow.mk f).cechNerve.obj (op n)) (RingHom.id _) p hp (h (op n) (op ⊤))
      (h (op n)) (schemeCechTupleOpen f U (op n)))
    haveI : Mono ε := (ModuleCat.mono_iff_injective _).mpr
      (affineCechNerveTuple_augmentation_injective f U p hp h hU hcU n)
    exact mono_comp _ ε
  | succ b =>
    exact (HomologicalComplex.isZero_single_obj_X up 0
      (ModuleCat.of ℤ (FrobeniusDirectLimit
        Γ((Arrow.mk f).cechNerve.obj (op n), ⊤) p hp (h (op n) (op ⊤))))
      (b + 1) (by omega)).mono _

/-- 同じΓのFrobenius係数をsingleへ入れた図式の交代余面複体。 -/
def schemePerfectCechTupleGlobalDouble :
    HomologicalComplex₂ (ModuleCat.{u} ℤ) up up :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).obj
    (frobeniusRingDiagram ((Arrow.mk f).cechNerve.rightOp ⋙ Scheme.Γ) p hp
      (fun n ↦ h (op n) (op ⊤)) ⋙ HomologicalComplex.single (ModuleCat.{u} ℤ) up 0)

/-- 同じ自然なΓ増大を交代余面関手へ渡した、実際の二重複体の射。 -/
def schemePerfectCechTupleGlobalDoubleMap :
    schemePerfectCechTupleGlobalDouble f p hp h ⟶
      (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).obj
        (schemePerfectCechTupleFunctor f U p hp h) :=
  (alternatingCofaceMapComplex (CochainComplex (ModuleCat.{u} ℤ) ℕ)).map
    (schemePerfectCechTupleGlobalAugmentation f U p hp h)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ実際のΓ増大のtotalは擬同型であるČech版。
Stacks 30.2.6 に対応する各列の比較を使う。
分離的なスキームの準連接層ではアフィン被覆のČechと一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem affineCechNerveTupleGlobalTotal_quasiIso
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    QuasiIso (HomologicalComplex₂.total.map
      (schemePerfectCechTupleGlobalDoubleMap f U p hp h) up) := by
  apply cechIntegerLiftTotal_quasiIso_of_mono_columns
  · intro a
    exact affineCechNerveTupleGlobalAugmentation_quasiIso f U p hp h hU hcU ⦋a⦌
  · intro a b
    exact (ModuleCat.mono_iff_injective _).mp
      (affineCechNerveTupleGlobalAugmentation_mono_f f U p hp h hU hcU ⦋a⦌ b)

end SerrePositivity.AlgebraicGeometry

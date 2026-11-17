module

public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleAffine
public import SerrePositivity.AlgebraicGeometry.AffinePerfectCechAugmentation

/-!
概要：アフィン射の同じ実際の nerve 項で、大域切断からのタプル Čech 増大を計算する。
方針：アフィン図式の極限、同じタプル開のアフィン性と被覆性を使う。
規約：既存の増大と同じ微分の Čech 版、層 Hⁱ との比較は作らない。
使われ方：環の conerve と同じ二重 Čech の各列の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u
variable {Y S : Scheme.{u}} (f : Y ⟶ S) [IsAffine Y] [IsAffine S]

set_option backward.isDefEq.respectTransparency false in
/-- アフィンな二つのスキームの同じ実際の Čech nerve の各項はアフィン。 -/
theorem affineCechNerve_isAffine (n : SimplexCategoryᵒᵖ) :
    IsAffine ((Arrow.mk f).cechNerve.obj n) := by
  let D := WidePullbackShape.wideCospan S
    (fun _ : Fin (n.unop.len + 1) ↦ Y) (fun _ ↦ f)
  haveI (j : WidePullbackShape (Fin (n.unop.len + 1))) : IsAffine (D.obj j) := by
    cases j with
    | none => change IsAffine S; infer_instance
    | some j => change IsAffine Y; infer_instance
  exact Scheme.isAffine_of_isLimit (limit.cone D) (limit.isLimit D)

variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Y.Opens)
variable (p : ℕ) (hp : p.Prime)
variable (h : ∀ n : SimplexCategoryᵒᵖ,
  ∀ O, (p : ((Arrow.mk f).cechNerve.obj n).presheaf.obj O) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 同じアフィン nerve 項の実際の恒等スカラーのタプル増大は単射。
Stacks 30.2.6 に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineCechNerveTuple_augmentation_injective
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) (n : SimplexCategory) :
    letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
    Function.Injective (schemeStructurePerfectCechAugmentation
        ((Arrow.mk f).cechNerve.obj (op n)) (RingHom.id _) p hp (h (op n) (op ⊤))
        (h (op n)) (schemeCechTupleOpen f U (op n))) := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  haveI := affineCechNerve_isAffine f (op n)
  exact affineSchemeStructurePerfectCechAugmentation_injective
    ((Arrow.mk f).cechNerve.obj (op n)) p hp (h (op n))
    (schemeCechTupleOpen f U (op n))
    (schemeCechTupleOpen_isAffine f U hU n.len)
    (schemeCechTupleOpen_iSup f U hcU (op n))

set_option backward.isDefEq.respectTransparency false in
/-- 同じアフィン nerve 項の実際のタプル増大と零次の微分は完全。
Stacks 30.2.6 に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineCechNerveTuple_augmentation_exact
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) (n : SimplexCategory) :
    letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
    Function.Exact (schemeStructurePerfectCechAugmentation
        ((Arrow.mk f).cechNerve.obj (op n)) (RingHom.id _) p hp (h (op n) (op ⊤))
        (h (op n)) (schemeCechTupleOpen f U (op n)))
      ((fullCechComplex (openCoverCechDiagram
        (frobeniusRingDiagram ((Arrow.mk f).cechNerve.obj (op n)).presheaf p hp (h (op n)))
        (schemeCechTupleOpen f U (op n)))).d 0 1).hom := by
  letI := cechFiniteIndexOrder (Fin (n.len + 1) → ι)
  haveI := affineCechNerve_isAffine f (op n)
  exact affineSchemeStructurePerfectCechAugmentation_exact
    ((Arrow.mk f).cechNerve.obj (op n)) p hp (h (op n))
    (schemeCechTupleOpen f U (op n))
    (schemeCechTupleOpen_isAffine f U hU n.len)
    (schemeCechTupleOpen_iSup f U hcU (op n))

/-- 同じアフィン nerve 項の全てのタプル次数の Frobenius 係数の完全性。
Stacks 30.2.6 に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineCechNerveTuple_augmentedExact
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) (n : SimplexCategory) :
    Function.Injective (fullCechDifferential
      (openCoverCechDiagram
        (frobeniusRingDiagram ((Arrow.mk f).cechNerve.obj (op n)).presheaf p hp (h (op n)))
        (schemeCechTupleOpen f U (op n))) 0) ∧
      ∀ k, Function.Exact (fullCechDifferential
        (openCoverCechDiagram
          (frobeniusRingDiagram ((Arrow.mk f).cechNerve.obj (op n)).presheaf p hp (h (op n)))
          (schemeCechTupleOpen f U (op n))) k)
        (fullCechDifferential
          (openCoverCechDiagram
            (frobeniusRingDiagram ((Arrow.mk f).cechNerve.obj (op n)).presheaf p hp (h (op n)))
            (schemeCechTupleOpen f U (op n))) (k + 1)) := by
  haveI := affineCechNerve_isAffine f (op n)
  exact affineSchemeStructurePerfectCech_augmentedExact
    ((Arrow.mk f).cechNerve.obj (op n)) p hp (h (op n))
    (schemeCechTupleOpen f U (op n))
    (schemeCechTupleOpen_isAffine f U hU n.len)
    (schemeCechTupleOpen_iSup f U hcU (op n))

end SerrePositivity.AlgebraicGeometry

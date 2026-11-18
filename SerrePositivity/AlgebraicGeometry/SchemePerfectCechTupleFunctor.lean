module

public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleCover
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechRefinedComposition
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechRefinedIdentity

/-!
概要：同じタプル被覆と実際の引き戻しを、Čech nerve の係数図式にまとめる。
方針：幾何的 nerve の射と添字の前合成に、検証済みの単位・合成則を渡す。
規約：各次数で独立な係数比較を選ばず、実際の切断の写像を保持する。
使われ方：B1 の二重 Čech の二方向の可換な微分の供給。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type} [DecidableEq ι]
variable (U : ι → X.Opens) (p : ℕ) (hp : p.Prime)
variable (h : ∀ n : SimplexCategoryᵒᵖ,
  ∀ O, (p : ((Arrow.mk f).cechNerve.obj n).presheaf.obj O) = 0)

/-- 同じタプル被覆の、実際の構造層の Frobenius 係数の複体。 -/
def schemePerfectCechTupleComplex (n : SimplexCategory) :
    CochainComplex (ModuleCat.{u} ℤ) ℕ :=
  fullCechComplex (openCoverCechDiagram
    (frobeniusRingDiagram ((Arrow.mk f).cechNerve.obj (op n)).presheaf p hp (h (op n)))
    (schemeCechTupleOpen f U (op n)))

/-- 幾何的 nerve の実際の射を、同じタプルの添字の前合成で引き戻す。 -/
def schemePerfectCechTupleMap {m n : SimplexCategory} (a : m ⟶ n) :
    schemePerfectCechTupleComplex f U p hp h m ⟶
      schemePerfectCechTupleComplex f U p hp h n :=
  schemeStructurePerfectCechRefinedPullbackMap ((Arrow.mk f).cechNerve.map a.op)
    p hp (h (op m)) (h (op n)) (schemeCechTupleOpen f U (op m))
    (schemeCechTupleOpen f U (op n)) (fun t j ↦ t (a.toOrderHom j))
    (schemeCechTupleOpen_map_le f U a.op)

set_option backward.isDefEq.respectTransparency false in
/-- 同じタプルの係数の写像は単位を保つ。 -/
theorem schemePerfectCechTupleMap_id (n : SimplexCategory) :
    schemePerfectCechTupleMap f U p hp h (𝟙 n) =
      𝟙 (schemePerfectCechTupleComplex f U p hp h n) := by
  have he : (Arrow.mk f).cechNerve.map (𝟙 n).op =
      𝟙 ((Arrow.mk f).cechNerve.obj (op n)) := by
    rw [op_id]
    exact (Arrow.mk f).cechNerve.map_id (op n)
  exact schemeStructurePerfectCechRefinedPullbackMap_eq_id_of_eq
    ((Arrow.mk f).cechNerve.map (𝟙 n).op) he p hp (h (op n))
    (schemeCechTupleOpen f U (op n)) (fun t j ↦ t ((𝟙 n : n ⟶ n).toOrderHom j)) rfl
    (schemeCechTupleOpen_map_le f U (𝟙 n).op)

set_option backward.isDefEq.respectTransparency false in
/-- 同じタプルの係数の写像は実際の nerve の射の合成を保つ。 -/
theorem schemePerfectCechTupleMap_comp {l m n : SimplexCategory}
    (a : l ⟶ m) (b : m ⟶ n) :
    schemePerfectCechTupleMap f U p hp h (a ≫ b) =
      schemePerfectCechTupleMap f U p hp h a ≫ schemePerfectCechTupleMap f U p hp h b := by
  have he : (Arrow.mk f).cechNerve.map b.op ≫ (Arrow.mk f).cechNerve.map a.op =
      (Arrow.mk f).cechNerve.map (a ≫ b).op := by
    rw [op_comp, Functor.map_comp]
  exact (schemeStructurePerfectCechRefinedPullbackMap_compIndex
    ((Arrow.mk f).cechNerve.map a.op) ((Arrow.mk f).cechNerve.map b.op)
    ((Arrow.mk f).cechNerve.map (a ≫ b).op) he p hp (h (op l)) (h (op m)) (h (op n))
    (schemeCechTupleOpen f U (op l)) (schemeCechTupleOpen f U (op m))
    (schemeCechTupleOpen f U (op n)) (fun t j ↦ t (a.toOrderHom j))
    (fun t j ↦ t (b.toOrderHom j)) (schemeCechTupleOpen_map_le f U a.op)
    (schemeCechTupleOpen_map_le f U b.op)
    (schemeCechTupleOpen_map_le f U (a ≫ b).op)).symm

/-- 同じタプル被覆の実際の係数の複体と引き戻しの関手。 -/
def schemePerfectCechTupleFunctor : SimplexCategory ⥤ CochainComplex (ModuleCat.{u} ℤ) ℕ where
  obj := schemePerfectCechTupleComplex f U p hp h
  map := schemePerfectCechTupleMap f U p hp h
  map_id := schemePerfectCechTupleMap_id f U p hp h
  map_comp := schemePerfectCechTupleMap_comp f U p hp h

end SerrePositivity.AlgebraicGeometry

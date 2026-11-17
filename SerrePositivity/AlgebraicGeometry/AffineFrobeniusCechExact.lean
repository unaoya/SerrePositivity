module

public import SerrePositivity.HomologicalAlgebra.Cech.Composition
public import SerrePositivity.HomologicalAlgebra.Cech.Filtered
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitMap
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Functor.OfSequence

/-!
概要：忠実平坦なアフィン射の実際の Čech 完全性と、その Frobenius 反復系の余極限。
方針：B1 の忠実平坦な底変換の反映・切断・filtered 余極限を使う。
規約：元の矢印と既存の Frobenius 写像を保つ。
使われ方：v 降下の判定で用いる fppf の完全性と Frobenius 係数への接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory Limits
open scoped TensorProduct
universe u

/-- 忠実平坦な実際のアフィン射の増大 Čech 複体は完全。 -/
theorem affineRingCechExact_of_faithfullyFlat {A : CommRingCat.{u}} (B : Under A)
    [Module.FaithfullyFlat A B.right] : SerrePositivity.Cech.IsCechExact (Arrow.mk B.hom) :=
  (SerrePositivity.Cech.isCechExact_baseChange_iff B.right B).mp
    (SerrePositivity.Cech.isCechExact_baseChange_of_map B B (𝟙 B))

/-- 同じ algebraMap の Under の加群構造へ、忠実平坦性を移す。 -/
theorem faithfullyFlat_mkUnder {R : CommRingCat.{u}} {S : Type u}
    [CommRing S] [Algebra R S] [Module.FaithfullyFlat R S] :
    Module.FaithfullyFlat R (CommRingCat.mkUnder R S) := by
  change (letI := (algebraMap R S).toAlgebra
    Module.FaithfullyFlat R S)
  rw [toAlgebra_algebraMap]
  infer_instance

/-- 忠実平坦な射の任意の底変換の増大 Čech 複体も完全。 -/
theorem affineRingCechExact_baseChange_of_faithfullyFlat {A : CommRingCat.{u}} (B : Under A)
    [Module.FaithfullyFlat A B.right] (D : CommRingCat.{u}) [Algebra A D] :
    SerrePositivity.Cech.IsCechExact (Arrow.mk ((CommRingCat.tensorProd A D).obj B).hom) := by
  have : Module.FaithfullyFlat D (D ⊗[A] B.right) := inferInstance
  have : Module.FaithfullyFlat D ((CommRingCat.tensorProd A D).obj B) :=
    faithfullyFlat_mkUnder (R := D) (S := D ⊗[A] B.right)
  exact affineRingCechExact_of_faithfullyFlat ((CommRingCat.tensorProd A D).obj B)

/-- 元の基底の標数条件は、同じ Under の射の先にも保たれる。 -/
theorem underPrimeCast_eq_zero {A : CommRingCat.{u}} (B : Under A) (p : ℕ)
    (hA : (p : A) = 0) : (p : B.right) = 0 := by
  rw [← map_natCast B.hom.hom, hA, map_zero]

/-- 既存の Frobenius 環写像は、元の矢印上の可換な自己射を与える。 -/
def frobeniusArrowStep (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hA : (p : f.left) = 0) (hB : (p : f.right) = 0) : f ⟶ f :=
  Arrow.homMk
    (CommRingCat.ofHom (frobeniusDirectSystemMap f.left p hp hA 0 1 (by decide)))
    (CommRingCat.ofHom (frobeniusDirectSystemMap f.right p hp hB 0 1 (by decide))) (by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro x
      exact frobeniusDirectSystemMap_naturality p hp hA hB f.hom.hom 0 1 (by decide) x)

/-- 元の矢印と同じ二つの環の Frobenius の反復系。 -/
def frobeniusArrowDiagram (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hA : (p : f.left) = 0) (hB : (p : f.right) = 0) : ℕ ⥤ Arrow CommRingCat.{u} :=
  Functor.ofSequence (fun _ : ℕ ↦ frobeniusArrowStep f p hp hA hB)

/-- 同じ自然数の反復系を、環と同じ宇宙の小圏で添字づける。 -/
def frobeniusArrowSmallDiagram (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
    (hA : (p : f.left) = 0) (hB : (p : f.right) = 0) :
    AsSmall.{u} ℕ ⥤ Arrow CommRingCat.{u} :=
  AsSmall.down ⋙ frobeniusArrowDiagram f p hp hA hB

/-- 忠実平坦なアフィン射の Frobenius 反復系の実際の余極限は Čech 完全。
各次数の Frobenius 順極限との比較は既存の conerve の余極限保存で接続する。 -/
theorem isCechExact_frobeniusArrowColimit_of_faithfullyFlat {A : CommRingCat.{u}}
    (B : Under A) [Module.FaithfullyFlat A B.right] (p : ℕ) (hp : p.Prime)
    (hA : (p : A) = 0) :
    SerrePositivity.Cech.IsCechExact
      (colimit (frobeniusArrowSmallDiagram (Arrow.mk B.hom) p hp hA
        (underPrimeCast_eq_zero B p hA))) := by
  have : IsFiltered (AsSmall.{u} ℕ) :=
    IsFiltered.of_equivalence (AsSmall.equiv : ℕ ≌ AsSmall.{u} ℕ)
  apply SerrePositivity.Cech.isCechExact_colimit
  intro j
  exact affineRingCechExact_of_faithfullyFlat B

/-- 任意の底変換後も、同じ Frobenius 反復系の余極限の Čech 複体は完全。 -/
theorem isCechExact_frobeniusArrowBaseChangeColimit_of_faithfullyFlat {A : CommRingCat.{u}}
    (B : Under A) [Module.FaithfullyFlat A B.right] (D : CommRingCat.{u}) [Algebra A D]
    (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) :
    let hD : (p : D) = 0 := by rw [← map_natCast (algebraMap A D), hA, map_zero]
    SerrePositivity.Cech.IsCechExact
      (colimit (frobeniusArrowSmallDiagram
        (Arrow.mk ((CommRingCat.tensorProd A D).obj B).hom) p hp hD
          (underPrimeCast_eq_zero ((CommRingCat.tensorProd A D).obj B) p hD))) := by
  have : Module.FaithfullyFlat D (D ⊗[A] B.right) := inferInstance
  have : Module.FaithfullyFlat D ((CommRingCat.tensorProd A D).obj B) :=
    faithfullyFlat_mkUnder (R := D) (S := D ⊗[A] B.right)
  exact isCechExact_frobeniusArrowColimit_of_faithfullyFlat
    ((CommRingCat.tensorProd A D).obj B) p hp
      (by rw [← map_natCast (algebraMap A D), hA, map_zero])

end SerrePositivity.AlgebraicGeometry

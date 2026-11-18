module

public import SerrePositivity.AlgebraicGeometry.FrobeniusConervePerfectNaturality
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitCechExact

/-!
概要：元の増大 conerve の実際の Frobenius 係数を、同じ増大環図式として比較する。
方針：同じ係数環と写像をまとめ、検証した自然な標準同型と B1 の同型不変性を使う。
規約：最終の AugmentedRingCechExact の型・定義は変えない。
使われ方：G4 の忠実平坦なアフィン射とその任意の底変換の係数の完全性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0)

/-- 同じ conerve の実際の各環と環準同型の Frobenius 順極限の余単体図式。 -/
def frobeniusRingConerve : CosimplicialObject CommRingCat.{u} where
  obj n := CommRingCat.of (FrobeniusDirectLimit (f.cechConerve.obj n) p hp
    (frobeniusConerve_primeCast f p hA n))
  map {n m} a := CommRingCat.ofHom (frobeniusDirectLimitMap p hp
    (frobeniusConerve_primeCast f p hA n) (frobeniusConerve_primeCast f p hA m)
    (f.cechConerve.map a).hom)
  map_id n := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk
      (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n)) z
    change frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n) i ((f.cechConerve.map (𝟙 n)).hom x) =
      frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n) i x
    rw [f.cechConerve.map_id]
    rfl
  map_comp {l m n} a b := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro z
    obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk
      (frobeniusDirectSystemMap (f.cechConerve.obj l) p hp
        (frobeniusConerve_primeCast f p hA l)) z
    change frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n) i ((f.cechConerve.map (a ≫ b)).hom x) =
      frobeniusDirectLimitOf (f.cechConerve.obj n) p hp
        (frobeniusConerve_primeCast f p hA n) i
          ((f.cechConerve.map b).hom ((f.cechConerve.map a).hom x))
    rw [f.cechConerve.map_comp]
    rfl

/-- 同じ基底の順極限と、元の増大写像の順極限写像を持つ増大環図式。 -/
def frobeniusAugmentedRingCoefficients : CosimplicialObject.Augmented CommRingCat.{u} where
  left := CommRingCat.of (FrobeniusDirectLimit f.left p hp hA)
  right := frobeniusRingConerve f p hp hA
  hom :=
    { app := fun n ↦ CommRingCat.ofHom (frobeniusDirectLimitMap p hp hA
        (frobeniusConerve_primeCast f p hA n) (f.augmentedCechConerve.hom.app n).hom)
      naturality := by
        intro n m a
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro z
        obtain ⟨i, x, rfl⟩ := DirectLimit.exists_eq_mk (frobeniusDirectSystemMap f.left p hp hA) z
        change frobeniusDirectLimitOf (f.cechConerve.obj m) p hp
            (frobeniusConerve_primeCast f p hA m) i
              ((f.augmentedCechConerve.hom.app m).hom x) =
          frobeniusDirectLimitOf (f.cechConerve.obj m) p hp
            (frobeniusConerve_primeCast f p hA m) i
              ((f.cechConerve.map a).hom ((f.augmentedCechConerve.hom.app n).hom x))
        exact congrArg (fun k : f.left ⟶ f.cechConerve.obj m ↦
          frobeniusDirectLimitOf (f.cechConerve.obj m) p hp
            (frobeniusConerve_primeCast f p hA m) i (k.hom x))
              (f.augmentedCechConerve.hom.naturality a) }

variable (hB : (p : f.right) = 0)

/-- 同じ各次数の標準比較は、元の全ての射を保つ環の余単体図式の同型。 -/
def frobeniusRingConerveIso : frobeniusRingConerve f p hp hA ≅
    (Arrow.mk (CommRingCat.ofHom
      (frobeniusDirectLimitMap p hp hA hB f.hom.hom))).cechConerve :=
  NatIso.ofComponents (frobeniusConervePerfectIso f p hp hA hB)
    (fun a ↦ frobeniusConervePerfectIso_naturality f p hp hA hB a)

set_option backward.isDefEq.respectTransparency false in
/-- 同じ基底の恒等比較と検証した増大の可換性を保つ、同じ増大環図式の標準同型。 -/
def frobeniusAugmentedRingCoefficientsIso : frobeniusAugmentedRingCoefficients f p hp hA ≅
    (Arrow.mk (CommRingCat.ofHom
      (frobeniusDirectLimitMap p hp hA hB f.hom.hom))).augmentedCechConerve :=
  Comma.isoMk (Iso.refl _) (frobeniusRingConerveIso f p hp hA hB) (by
    apply NatTrans.ext
    funext n
    change 𝟙 _ ≫ (Arrow.mk (CommRingCat.ofHom
        (frobeniusDirectLimitMap p hp hA hB f.hom.hom))).augmentedCechConerve.hom.app n =
      CommRingCat.ofHom (frobeniusDirectLimitMap p hp hA
        (frobeniusConerve_primeCast f p hA n) (f.augmentedCechConerve.hom.app n).hom) ≫
          (frobeniusConervePerfectIso f p hp hA hB n).hom
    rw [Category.id_comp]
    exact (frobeniusConervePerfectIso_augmentation f p hp hA hB n).symm)

/-- 同じ係数の増大環図式と実際の矢印の完全性を、B1 の同じ定義で比較する。 -/
theorem frobeniusAugmentedRingCoefficients_exact_iff :
    SerrePositivity.Cech.AugmentedRingCechExact (frobeniusAugmentedRingCoefficients f p hp hA) ↔
      SerrePositivity.Cech.IsCechExact (Arrow.mk (CommRingCat.ofHom
        (frobeniusDirectLimitMap p hp hA hB f.hom.hom))) :=
  SerrePositivity.Cech.ringCechExact_iff_of_iso (frobeniusAugmentedRingCoefficientsIso f p hp hA hB)

/-- 忠実平坦な元のアフィン射の、同じ実際の各環の Frobenius 係数の増大 Čech 完全性。 -/
theorem frobeniusAugmentedRingCoefficients_exact_of_faithfullyFlat {A : CommRingCat.{u}}
    (B : Under A) [Module.FaithfullyFlat A B.right] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (Arrow.mk B.hom) p hp hA) :=
  (frobeniusAugmentedRingCoefficients_exact_iff (Arrow.mk B.hom) p hp hA
    (underPrimeCast_eq_zero B p hA)).mpr
      (isCechExact_frobeniusDirectLimit_of_faithfullyFlat B p hp hA)

/-- 元の忠実平坦な射の任意の底変換にも、同じ Frobenius 係数の完全性を供給する。 -/
theorem frobeniusAugmentedRingCoefficients_exact_baseChange_of_faithfullyFlat
    {A : CommRingCat.{u}} (B : Under A) [Module.FaithfullyFlat A B.right]
    (D : CommRingCat.{u}) [Algebra A D] (p : ℕ) (hp : p.Prime) (hA : (p : A) = 0) :
    let hD : (p : D) = 0 := by rw [← map_natCast (algebraMap A D), hA, map_zero]
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients
        (Arrow.mk ((CommRingCat.tensorProd A D).obj B).hom) p hp hD) := by
  have : Module.FaithfullyFlat D (D ⊗[A] B.right) := inferInstance
  have : Module.FaithfullyFlat D ((CommRingCat.tensorProd A D).obj B) :=
    faithfullyFlat_mkUnder (R := D) (S := D ⊗[A] B.right)
  exact frobeniusAugmentedRingCoefficients_exact_of_faithfullyFlat
    ((CommRingCat.tensorProd A D).obj B) p hp
      (by rw [← map_natCast (algebraMap A D), hA, map_zero])

end SerrePositivity.AlgebraicGeometry

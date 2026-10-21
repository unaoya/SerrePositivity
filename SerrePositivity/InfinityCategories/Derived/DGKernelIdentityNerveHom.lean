module
public import SerrePositivity.InfinityCategories.Derived.DGKernelIdentityInfinity
public import SerrePositivity.InfinityCategories.Derived.DGBimoduleIsoNerveAlgebra
public import SerrePositivity.InfinityCategories.Derived.FunctorHomotopyRawTransport
/-!
概要：元の通常 kernel 単位と同じ単位子の nerve 像を照合する。
方針：元の指定値と端点等式を保つ。
規約：原 Hom の平坦性を追加しない。使われ方：kernel の単位・結合 coherence。
-/
@[expose] public section
open CategoryTheory
universe u v
namespace SerrePositivity.InfinityCategories
open DifferentialGraded DGNerve SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
/-- 元の通常単位は、同じ双加群単位子の nerve 像の指定値を保つ。 -/
lemma dgKernelIdentityNerveIso_value_heq :
    HEq (dgKernelIdentityNerveIso R D)
      (dgBimoduleIsoNerve R D (RightModule R D)
        (BimoduleTensor.leftBimoduleUnitIso R D (RightModule R D)
          (DGFunctor.id (RightModule R D)))) := by
  simp only [dgKernelIdentityNerveIso]
  rfl
/-- 元の通常単位の射は、同じ単位子の全関手射の像を保つ。 -/
lemma dgKernelIdentityNerveIso_hom_heq :
    HEq (dgKernelIdentityNerveIso R D).hom
      ((dgBimoduleFunctorHomFunctor R D (RightModule R D)).map
        (BimoduleTensor.leftBimoduleUnitIso R D (RightModule R D)
          (DGFunctor.id (RightModule R D))).hom) := by
  have hh := functorIso_hom_heq (dgKernelIdentityNerveIso R D)
    (dgBimoduleIsoNerve R D (RightModule R D)
      (BimoduleTensor.leftBimoduleUnitIso R D (RightModule R D)
        (DGFunctor.id (RightModule R D)))) rfl dgNerve.map_id.symm
    (dgKernelIdentityNerveIso_value_heq R D)
  rw [← dgBimoduleFunctorHomFunctor_mapIso] at hh
  exact hh
end
end SerrePositivity.InfinityCategories

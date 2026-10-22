module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFHomotopyFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFDGKIntegerNaturality

/-! # 元の dgK 射による整数群関手と同じ実比較の自然同型
概要：元の実 Perf 延長による dgKMap の整数 π 作用は、厳密 dg 入力に関して関手になる。
方針：同じ実比較射の全単射と入力自然性で、新 BF 射の厳密な関手法則を反映する。
規約：通常の射は元の dgKMap の作用そのもの。使われ方：既存の整数 K 群界面。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Spectra
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の dgK 射の整数 π 作用は、恒等 dg 入力の恒等作用を保つ。 -/
lemma dgKHomotopyMap_id (X : PerfDGInput.{u, v} A) (j : ℤ) :
    OmegaSpectrum.homotopyMap
      (dgKMap A X X (SerrePositivity.DifferentialGraded.DGFunctor.id X)) j =
        MonoidHom.id _ := by
  apply MonoidHom.ext
  intro a
  obtain ⟨b, rfl⟩ := (presentedPerfectDGBFDGKGroupEquiv A X j).surjective a
  have h := presentedPerfectDGBFDGKGroupEquiv_naturality A (𝟙 X) j b
  rw [presentedPerfectDGBFMap_id, OmegaSpectrum.homotopyMap_id] at h
  exact h

/-- 元の dgK 射の整数 π 作用は、厳密 dg 入力の合成を保つ。 -/
lemma dgKHomotopyMap_comp {X Y Z : PerfDGInput.{u, v} A}
    (f : X ⟶ Y) (g : Y ⟶ Z) (j : ℤ) :
    OmegaSpectrum.homotopyMap (dgKMap A X Z (f ≫ g).down) j =
      (OmegaSpectrum.homotopyMap (dgKMap A Y Z g.down) j).comp
        (OmegaSpectrum.homotopyMap (dgKMap A X Y f.down) j) := by
  apply MonoidHom.ext
  intro a
  obtain ⟨b, rfl⟩ := (presentedPerfectDGBFDGKGroupEquiv A X j).surjective a
  change OmegaSpectrum.homotopyMap (dgKMap A X Z (f ≫ g).down) j
      (presentedPerfectDGBFDGKGroupEquiv A X j b) =
    OmegaSpectrum.homotopyMap (dgKMap A Y Z g.down) j
      (OmegaSpectrum.homotopyMap (dgKMap A X Y f.down) j
        (presentedPerfectDGBFDGKGroupEquiv A X j b))
  rw [presentedPerfectDGBFDGKGroupEquiv_naturality,
    presentedPerfectDGBFDGKGroupEquiv_naturality,
    presentedPerfectDGBFDGKGroupEquiv_naturality,
    presentedPerfectDGBFMap_comp, OmegaSpectrum.homotopyMap_comp]
  rfl

/-- 元の dgKMap の全整数 π 作用そのものによる可換群値関手。 -/
def dgKHomotopyFunctor (j : ℤ) : PerfDGInput.{u, v} A ⥤ CommGrpCat.{max (u + 1) v} where
  obj X := CommGrpCat.of (dgKGroup A X j)
  map {X Y} f := CommGrpCat.ofHom (OmegaSpectrum.homotopyMap (dgKMap A X Y f.down) j)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro a
    exact DFunLike.congr_fun (dgKHomotopyMap_id A X j) a
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact DFunLike.congr_fun (dgKHomotopyMap_comp A f g j) a

/-- 新 BF K と元の dgK の整数群関手の自然同型は、同じ実比較射によるもの。 -/
def presentedPerfectDGBFDGKHomotopyNatIso (j : ℤ) :
    presentedPerfectDGBFHomotopyFunctor A j ≅ dgKHomotopyFunctor A j :=
  NatIso.ofComponents (fun X => (presentedPerfectDGBFDGKGroupEquiv A X j).toCommGrpIso) (by
    intro X Y f
    apply ConcreteCategory.hom_ext
    intro a
    exact (presentedPerfectDGBFDGKGroupEquiv_naturality A f j a).symm)

end SerrePositivity.KST.SConstruction

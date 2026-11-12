module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGBFMap
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.StrictSimplicialOrdinaryFunctor
public import SerrePositivity.KST.Spectra.SpectrumHomotopyFunctor

/-! # 同じ厳密 dg BF K と整数 K 群の通常の関手
概要：実 BF 豊穣関手から同じ通常 dg 射の BF 関手と全整数 K 群の関手を取り出す。
方針：元の全 Hom による通常射回収と、BF の整数 π 関手を合成する。
規約：高次入力は豊穣関手に保持する。使われ方：K-基盤の整数群界面。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
variable (A : Type u) [CommRing A]

/-- 実 BF 値の元の通常射との同値を使う。 -/
local instance presentedPerfectDGBFOrdinaryTarget_simplicialCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 同じ実 BF 厳密豊穣関手から取り出した通常のスペクトル値関手。 -/
def presentedPerfectDGBFOrdinaryFunctor :
    PerfDGInput.{u, v} A ⥤ OmegaSpectrum.{max (u + 1) v} :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.strictSimplicialOrdinaryFunctor (presentedPerfectDGBFEnrichedFunctor A)

/-- 通常射の像は同じ元の厳密 dg 関手による実 BF 射。 -/
lemma presentedPerfectDGBFOrdinaryFunctor_map
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) :
    (presentedPerfectDGBFOrdinaryFunctor A).map f = presentedPerfectDGBFMap A f := rfl

/-- 同じ実 BF 射は通常 dg 入力の恒等射を厳密に保存する。 -/
lemma presentedPerfectDGBFMap_id (X : PerfDGInput.{u, v} A) :
    presentedPerfectDGBFMap A (𝟙 X) = 𝟙 (presentedPerfectDGBFOmegaSpectrum A X) :=
  (presentedPerfectDGBFOrdinaryFunctor A).map_id X

/-- 同じ実 BF 射は通常 dg 入力の合成を厳密に保存する。 -/
lemma presentedPerfectDGBFMap_comp {X Y Z : PerfDGInput.{u, v} A}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    presentedPerfectDGBFMap A (f ≫ g) =
      presentedPerfectDGBFMap A f ≫ presentedPerfectDGBFMap A g :=
  (presentedPerfectDGBFOrdinaryFunctor A).map_comp f g

/-- 元の実 BF K の全整数次数の可換群値関手。 -/
def presentedPerfectDGBFHomotopyFunctor (j : ℤ) :
    PerfDGInput.{u, v} A ⥤ CommGrpCat.{max (u + 1) v} :=
  presentedPerfectDGBFOrdinaryFunctor A ⋙ OmegaSpectrum.homotopyFunctor j

/-- 整数群関手の通常射は、同じ実 BF スペクトル射の誘導準同型。 -/
lemma presentedPerfectDGBFHomotopyFunctor_map (j : ℤ)
    {X Y : PerfDGInput.{u, v} A} (f : X ⟶ Y) :
    (presentedPerfectDGBFHomotopyFunctor A j).map f =
      CommGrpCat.ofHom (OmegaSpectrum.homotopyMap (presentedPerfectDGBFMap A f) j) := rfl

end SerrePositivity.KST.SConstruction

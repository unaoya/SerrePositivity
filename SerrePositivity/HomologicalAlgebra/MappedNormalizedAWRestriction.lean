module
public import SerrePositivity.HomologicalAlgebra.NormalizedEZMap

/-!
概要：raw AWの成分の等式を、元のMoore包含で正規化AWへ制限する。
方針：既存正規化AWの定義と包含・射影の分裂恒等式を合成する。
規約：P∞とAWの可換性を仮定せず、任意加法関手で係数を移す既存構成の法則。
使われ方：HA 1.2.4、IS-W2 B02の実合成と自由鎖AWの照合の分割。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.HomologicalAlgebra
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable {B : Type v} [Category.{w} B] [Abelian B]
variable (F : ModuleCat.{u} ℤ ⥤ B) [F.Additive]
variable (C D : SimplicialObject (ModuleCat.{u} ℤ))

/-- raw成分の等式は同じMoore包含の制限により指定正規化AWの成分を同定する。 -/
theorem mappedNormalizedAlexanderWhitney_f_eq_of_raw (n : ℕ) (T : B)
    (t : F.obj ((chainIntegerTensor ((normalizedMooreComplex _).obj C)
      ((normalizedMooreComplex _).obj D)).X n) ⟶ T)
    (h : ((normalizedMooreComplex B).obj (simplicialIntegerTensor C D ⋙ F)).X n ⟶ T)
    (hraw : F.map ((alexanderWhitney C D).f n ≫
        (chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
          (PInftyToNormalizedMooreComplex D)).f n) ≫ t =
      F.map ((PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)).f n) ≫
        (normalizedMooreMapIso F (simplicialIntegerTensor C D)).hom.f n ≫ h) :
    (mappedNormalizedAlexanderWhitney F C D).f n ≫ t = h := by
  let e := normalizedMooreMapIso F (simplicialIntegerTensor C D)
  have he : (mappedNormalizedAlexanderWhitney F C D).f n =
      e.inv.f n ≫ F.map ((normalizedAlexanderWhitney C D).f n) := rfl
  rw [he]
  apply (cancel_epi (e.hom.f n)).mp
  have hei : e.hom.f n ≫ e.inv.f n = 𝟙 _ :=
    congrArg (fun g => g.f n) e.hom_inv_id
  simp only [← Category.assoc]
  rw [hei, Category.id_comp]
  calc
    F.map ((normalizedAlexanderWhitney C D).f n) ≫ t =
        F.map ((inclusionOfMooreComplexMap (simplicialIntegerTensor C D)).f n) ≫
          (F.map ((alexanderWhitney C D).f n ≫
            (chainIntegerTensorMap (PInftyToNormalizedMooreComplex C)
              (PInftyToNormalizedMooreComplex D)).f n) ≫ t) := by
      simp only [normalizedAlexanderWhitney, comp_f, Functor.map_comp, Category.assoc]
    _ = F.map ((inclusionOfMooreComplexMap (simplicialIntegerTensor C D)).f n) ≫
        (F.map ((PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)).f n) ≫
          e.hom.f n ≫ h) := congrArg
            (fun k => F.map
              ((inclusionOfMooreComplexMap (simplicialIntegerTensor C D)).f n) ≫ k) hraw
    _ = e.hom.f n ≫ h := by
      have hs : (inclusionOfMooreComplexMap (simplicialIntegerTensor C D)).f n ≫
          (PInftyToNormalizedMooreComplex (simplicialIntegerTensor C D)).f n = 𝟙 _ :=
        congrArg (fun g => g.f n) (splitMonoInclusionOfMooreComplexMap
          (simplicialIntegerTensor C D)).id
      rw [← Category.assoc, ← Category.assoc, ← F.map_comp, hs, F.map_id,
        Category.id_comp]

end SerrePositivity.HomologicalAlgebra

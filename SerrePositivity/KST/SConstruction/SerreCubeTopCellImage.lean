module
public import SerrePositivity.KST.SConstruction.SerreCubeOrientedTopCell

/-! # 元の Serre 最高生成元の任意の Hom 複体への像
概要：任意の元の chain map の下で、HA 向きの最高生成元の像の微分式を回収する。
方針：同じ射の微分可換性を元の生成元で評価し、全面和の線形な像を取る。
規約：元の面射との実合成を保持。使われ方：Λ からの実 dg 関手の native HA 成分。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped BigOperators
variable (A : Type u) [CommRing A]

/-- 元の任意の chain map による、元の HA 向きの最高生成元の実像。 -/
def serreCubeTopCellImage (K : Complex A) (n : ℕ) (f : serreCubeComplex A n ⟶ K) :
    K.X (-(n : ℤ)) := f.f (-(n : ℤ)) (serreCubeOrientedTopCell A n)

/-- 元の最高生成元の実像の微分は、元の全ての面射との合成の同じ像の符号付き和。 -/
lemma serreCubeTopCellImage_d (K : Complex A) (n : ℕ)
    (f : serreCubeComplex A (n + 1) ⟶ K) :
    K.d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (serreCubeTopCellImage A K (n + 1) f) =
      ∑ i : Fin (n + 1), ((i.val : ℤ) + 1).negOnePow •
        (serreCubeTopCellImage A K n ((serreCubeFace A false n i).hom ≫ f) -
          serreCubeTopCellImage A K n ((serreCubeFace A true n i).hom ≫ f)) := by
  have hm (V W : ModuleCat.{u} A) (g : V ⟶ W) (F : Fin (n + 1) → V)
      (G : Fin (n + 1) → V) :
      g (∑ i : Fin (n + 1), ((i.val : ℤ) + 1).negOnePow • (F i - G i)) =
        ∑ i : Fin (n + 1), ((i.val : ℤ) + 1).negOnePow • (g (F i) - g (G i)) := by
    simp only [map_sum, Units.smul_def, map_zsmul, map_sub]
  have hc := ConcreteCategory.congr_hom
    (f.comm (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))) (serreCubeOrientedTopCell A (n + 1))
  exact hc.trans ((congrArg (fun z => f.f (-(n : ℤ)) z)
    (serreCubeOrientedTopCell_d A n)).trans (hm _ _ (f.f (-(n : ℤ))) _ _))

end SerrePositivity.KST.SConstruction

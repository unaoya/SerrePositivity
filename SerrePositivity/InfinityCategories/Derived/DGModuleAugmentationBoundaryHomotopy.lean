module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationCutHomotopy
/-!
概要：元の HA 線形・二次境界へ同じ実比較 cochain を適用し、実削除・切断補正和へ移す。
方針：全 cochain の線形性と同じ切断合成の二項式を使う。
規約：元の単体方程式はまだ仮定しない。使われ方：混合 prism の一般 HA 方程式。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C]
  (E : Type w) [DGCategory R E] [Small.{u} E] (F : DGFunctor R C (RightModule R E))
  {n : ℕ} (s : SimplexData R (DGModuleFunctorResolutionObject R C E F) n)
/-- 実線形境界の同じ比較成分は、実削除係数の同じ比較成分の符号付き和。 -/
lemma dgModuleAugmentationHomotopyAt_linearBoundary
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) :
    dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
      (s.linearBoundary I a b k) =
    ∑ j ∈ Index.interior I a b, Index.sign I j •
      dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
        (s.homOrZero (I.erase j) a b (k + 1)) := by
  simp only [SimplexData.linearBoundary, dgModuleAugmentationHomotopyAt,
    Units.smul_def, map_sum, map_zsmul]
/-- 実二次境界の同じ比較成分は、実左右補正の同じ二重和。 -/
lemma dgModuleAugmentationHomotopyAt_quadraticBoundary
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hk : k = 2 - (I.card : ℤ)) :
    dgModuleAugmentationHomotopyAt R C E F (s.obj a) (s.obj b) (k + 1) k (by omega)
      (s.quadraticBoundary I a b k) =
    ∑ j ∈ Index.interior I a b, Index.sign I j •
      ((2 - ((I.filter (j ≤ ·)).card : ℤ)).negOnePow •
        dgModuleAugmentationImageCut R C E F s I a b k j +
        dgModuleAugmentationHomotopyCut R C E F s I a b k j) := by
  simp only [SimplexData.quadraticBoundary, dgModuleAugmentationHomotopyAt,
    Units.smul_def, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjI : j ∈ I := (Finset.mem_filter.mp hj).1
  have hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ)) = k + 1 := by
    have := Index.split_card hjI
    omega
  have he := dgModuleAugmentationHomotopyAt_cutCompose R C E F s I a b k j hsum
  simpa only [dgModuleAugmentationHomotopyAt, Units.smul_def] using!
    congrArg (fun x ↦ Index.sign I j • x) he
end SerrePositivity.InfinityCategories

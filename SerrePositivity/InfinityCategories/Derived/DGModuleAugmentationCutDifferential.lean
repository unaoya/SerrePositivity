module
public import SerrePositivity.InfinityCategories.Derived.DGModuleAugmentationCorrection
/-!
概要：同じ全域切断補正の微分を、右の実比較成分と左の実入力像の二項へ展開する。
方針：次数の一致条件を評価し、既存の全 dg Leibniz 則を同じ実二因子へ適用する。
規約：入力の単体方程式を仮定しない。使われ方：一般 HA 方程式の切断補正の微分展開。
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
/-- 同じ実切断補正の、全整数次数での二項微分式。 -/
lemma dgModuleAugmentationHomotopyCut_differential
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ) (j : Fin (n + 1))
    (hsum : (2 - ((I.filter (· ≤ j)).card : ℤ)) +
      (2 - ((I.filter (j ≤ ·)).card : ℤ) - 1) = k) :
    let p := 2 - ((I.filter (· ≤ j)).card : ℤ)
    let q := 2 - ((I.filter (j ≤ ·)).card : ℤ)
    let l : GradedHom R (s.obj a).replacement.val (s.obj j).replacement.val p :=
      ((dgModuleAugmentationSource R C E F).map (s.obj a) (s.obj j)).f p
        (s.homOrZero (I.filter (· ≤ j)) a j p)
    let r : GradedHom R (s.obj j).replacement.val (F.obj (s.obj b).source) (q - 1) :=
      dgModuleAugmentationHomotopyComponent R C E F (s.obj j) (s.obj b) q
        (s.homOrZero (I.filter (j ≤ ·)) j b q)
    differential R (x := (s.obj a).replacement.val) (y := F.obj (s.obj b).source)
      (dgModuleAugmentationHomotopyCut R C E F s I a b k j) =
    compose R (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1)
      (differential R (x := (s.obj j).replacement.val) (y := F.obj (s.obj b).source) r)
      l (by dsimp [p, q] at *; omega) +
    (q - 1).negOnePow • compose R
      (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val)
      (z := F.obj (s.obj b).source) (n := k + 1) r
      (differential R (x := (s.obj a).replacement.val) (y := (s.obj j).replacement.val) l)
      (by dsimp [p, q] at *; omega) := by
  dsimp only
  rw [dgModuleAugmentationHomotopyCut, dite_eq_left hsum]
  exact differential_compose R _ _ hsum
end SerrePositivity.InfinityCategories

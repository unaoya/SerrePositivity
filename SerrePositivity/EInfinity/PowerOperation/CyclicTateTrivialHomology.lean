module

public import SerrePositivity.EInfinity.PowerOperation.CyclicTateComplex

/-!
# 周期係数複体の自明作用での指定ホモロジー比較

DAG XIII Construction 2.2.6 の指定 Tate 類の鎖レベルの前段。
群の位数が標数なら自明作用の微分は零なので、整数全次数のホモロジーを
元の係数加群と自然に比較する。native な Tate スペクトルとの同定は含めない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable {k : Type u} [CommRing k] {G : Type v} [CommGroup G] [Fintype G]

/-- 周期係数複体の台の加群複体の全関手。 -/
def cyclicTateModuleComplexFunctor (g : G) : Rep k G ⥤ CochainComplex (ModuleCat k) ℤ :=
  cyclicTateComplexFunctor g ⋙ (forget₂ (Rep k G) (ModuleCat k)).mapHomologicalComplex _

lemma cyclicTateModuleComplex_d_trivial (A : Rep k G) [A.IsTrivial]
    (p : ℕ) [CharP k p] (hp : Fintype.card G = p) (g : G) (i j : ℤ) :
    ((cyclicTateModuleComplexFunctor g).obj A).d i j = 0 := by
  change (forget₂ (Rep k G) (ModuleCat k)).map
    (CochainComplex.of.d (fun _ => A) (cyclicTateDifferential A g) i j) = 0
  simp only [CochainComplex.of.d]
  split_ifs with h
  · simp [cyclicTateDifferential_trivial A p hp g i]
  · simp

/-- 自明作用の周期係数複体の H^i と係数加群の指定同型。 -/
def cyclicTateTrivialHomologyIso (A : Rep k G) [A.IsTrivial]
    (p : ℕ) [CharP k p] (hp : Fintype.card G = p) (g : G) (i : ℤ) :
    ((cyclicTateModuleComplexFunctor g).obj A).homology i ≅ (forget₂ _ (ModuleCat k)).obj A :=
  let K := (cyclicTateModuleComplexFunctor g).obj A
  (K.isoHomologyπ (i - 1) i (by simp)
    (cyclicTateModuleComplex_d_trivial A p hp g _ _)).symm ≪≫
    K.iCyclesIso i (i + 1) (by simp) (cyclicTateModuleComplex_d_trivial A p hp g _ _)

lemma cyclicTateTrivialHomologyIso_pi (A : Rep k G) [A.IsTrivial]
    (p : ℕ) [CharP k p] (hp : Fintype.card G = p) (g : G) (i : ℤ) :
    ((cyclicTateModuleComplexFunctor g).obj A).homologyπ i ≫
      (cyclicTateTrivialHomologyIso A p hp g i).hom =
      ((cyclicTateModuleComplexFunctor g).obj A).iCycles i := by
  simp [cyclicTateTrivialHomologyIso]

/-- 同じホモロジー同型は全ての自明表現の射に自然。 -/
lemma cyclicTateTrivialHomologyIso_natural {A B : Rep k G} [A.IsTrivial] [B.IsTrivial]
    (f : A ⟶ B) (p : ℕ) [CharP k p] (hp : Fintype.card G = p) (g : G) (i : ℤ) :
    HomologicalComplex.homologyMap ((cyclicTateModuleComplexFunctor g).map f) i ≫
      (cyclicTateTrivialHomologyIso B p hp g i).hom =
      (cyclicTateTrivialHomologyIso A p hp g i).hom ≫ (forget₂ _ (ModuleCat k)).map f := by
  rw [← cancel_epi (((cyclicTateModuleComplexFunctor g).obj A).homologyπ i)]
  simp only [← Category.assoc, HomologicalComplex.homologyπ_naturality]
  rw [Category.assoc, cyclicTateTrivialHomologyIso_pi,
    cyclicTateTrivialHomologyIso_pi, HomologicalComplex.cyclesMap_i]
  rfl

/-- 自明作用を付けた全係数加群についての H^i 比較の自然同型。 -/
def cyclicTateTrivialHomologyNatIso (p : ℕ) [CharP k p]
    (hp : Fintype.card G = p) (g : G) (i : ℤ) :
    Rep.trivialFunctor k G ⋙ cyclicTateModuleComplexFunctor g ⋙
      HomologicalComplex.homologyFunctor _ _ i ≅ 𝟭 (ModuleCat k) :=
  NatIso.ofComponents
    (fun A => cyclicTateTrivialHomologyIso ((Rep.trivialFunctor k G).obj A) p hp g i)
    (fun f => cyclicTateTrivialHomologyIso_natural ((Rep.trivialFunctor k G).map f) p hp g i)

end SerrePositivity.EInfinity.PowerOperation

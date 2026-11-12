module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MooreZeroHomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# 非負鎖複体の零次ホモロジー類写像の自然性

DAG XIII §2.2 の π/H の代表元比較で用いる一般の補助。実 opcycles 射を保持する。
［一般∞］移動候補。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomologicalComplex
variable {A : Type u} [CommRing A]

/-- 非負鎖複体の零次の元を、同じ実ホモロジーへ送る類写像。 -/
def chainZeroClass (K : ChainComplex (ModuleCat A) ℕ) : K.X 0 ⟶ K.homology 0 :=
  K.pOpcycles 0 ≫ K.isoHomologyι₀.inv

/-- 類写像は全鎖写像に自然。 -/
@[reassoc]
lemma chainZeroClass_naturality {K L : ChainComplex (ModuleCat A) ℕ} (f : K ⟶ L) :
    chainZeroClass K ≫ homologyMap f 0 = f.f 0 ≫ chainZeroClass L := by
  rw [chainZeroClass, chainZeroClass, Category.assoc,
    ChainComplex.isoHomologyι₀_inv_naturality, ← Category.assoc,
    p_opcyclesMap, Category.assoc]

end SerrePositivity.EInfinity.PowerOperation

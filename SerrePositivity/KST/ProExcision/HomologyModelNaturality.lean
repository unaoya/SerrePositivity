module
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
@[expose] public noncomputable section
namespace SerrePositivity.KST.ProExcision
open CategoryTheory CategoryTheory.Limits
variable {C : Type*} [Category* C] [Abelian C]
/-- 概要：明示した核・ホモロジー模型上の二つの可換四角形から、標準ホモロジー射との比較を得る。
方針：左ホモロジー写像データを構成し、包含で相殺して境界の四角形も導く。
規約：模型は Mathlib の LeftHomologyData。使われ方：KST Lemma 4.10 の長完全列のホモロジー模型の自然性。 -/
theorem leftHomologyModelMap_comm
    {S T : ShortComplex C} (f : S ⟶ T)
    (hS : S.LeftHomologyData) (hT : T.LeftHomologyData)
    (k : hS.K ⟶ hT.K) (m : hS.H ⟶ hT.H)
    (hi : k ≫ hT.i = hS.i ≫ f.τ₂) (hπ : hS.π ≫ m = k ≫ hT.π) :
    ShortComplex.homologyMap f ≫ hT.homologyIso.hom = hS.homologyIso.hom ≫ m := by
  let γ : ShortComplex.LeftHomologyMapData f hS hT :=
    { φK := k
      φH := m
      commi := hi
      commπ := hπ
      commf' := by
        apply (cancel_mono hT.i).mp
        rw [Category.assoc, hi, ← Category.assoc, hS.f'_i,
          Category.assoc, hT.f'_i, f.comm₁₂] }
  exact γ.homologyMap_comm


end SerrePositivity.KST.ProExcision

module

public import SerrePositivity.EInfinity.Interface.Theory

/-!
# 零次の p 乗との一致の同型による移送

May, Proposition 2.3(iii) を局所化へ降ろすための補助。
環値関手とその台のホモロジー関手の自然同型を使い、P⁰ の零次の性質を同型で運ぶ。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {k : Type u} [CommRing k]
variable {C : Type v} [Category.{w} C]

/-- 零次環の自然比較のもとで、演算が p 乗を誘導するという性質。 -/
def MayZeroFrobeniusAt (p : ℕ) (P : C ⥤ RingAlgebra k) (H : C ⥤ AddCommGrpCat.{u})
    (e : P ⋙ discreteAlgebraModule k ⋙ forget₂ (ModuleCat k) AddCommGrpCat ≅ H)
    (α : H ⟶ H) (z : C) : Prop :=
  ∀ a : (P.obj z).right, α.app z (e.hom.app z a) = e.hom.app z (a ^ p)

/-- 全射に自然な同じ演算と環比較を使うと、零次の計算は対象の同型で運べる。 -/
lemma mayZeroFrobeniusAt_of_iso (p : ℕ) (P : C ⥤ RingAlgebra k)
    (H : C ⥤ AddCommGrpCat.{u})
    (e : P ⋙ discreteAlgebraModule k ⋙ forget₂ (ModuleCat k) AddCommGrpCat ≅ H)
    (α : H ⟶ H) {y z : C} (s : y ≅ z) (hy : MayZeroFrobeniusAt p P H e α y) :
    MayZeroFrobeniusAt p P H e α z := by
  intro a
  let b := (P.map s.inv).right.hom a
  have hab : (P.map s.hom).right.hom b = a := by
    have hh : P.map s.inv ≫ P.map s.hom = 𝟙 (P.obj z) := by
      rw [← P.map_comp, s.inv_hom_id, P.map_id]
    exact congrArg (fun f => f.right.hom a) hh
  have he (c : (P.obj y).right) :
      H.map s.hom (e.hom.app y c) = e.hom.app z ((P.map s.hom).right.hom c) :=
    (congrArg (fun f => f c) (e.hom.naturality s.hom)).symm
  calc
    α.app z (e.hom.app z a) = α.app z (H.map s.hom (e.hom.app y b)) := by rw [he, hab]
    _ = H.map s.hom (α.app y (e.hom.app y b)) :=
      congrArg (fun f => f (e.hom.app y b)) (α.naturality s.hom)
    _ = H.map s.hom (e.hom.app y (b ^ p)) := by rw [hy b]
    _ = e.hom.app z ((P.map s.hom).right.hom (b ^ p)) := he _
    _ = e.hom.app z (((P.map s.hom).right.hom b) ^ p) := by rw [map_pow]
    _ = e.hom.app z (a ^ p) := by rw [hab]

end SerrePositivity.EInfinity.PowerOperation

module

public import SerrePositivity.InfinityCategories.F2.Ind.FixedRelativeLiftBoundary

/-!
概要：指定制限の実 fiber の普遍族は、その指定領域と全ての部分領域で厳密に定値。
方針：実 fiber の固定条件と相対前合成の合成則を使う。
規約：同型の代表辺だけでなく全次数で固定。使われ方：終端区間固定の uncurry。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A T E B : SSet.{u}} (p : E ⟶ B) (b : A ⟶ B) (i : T ⟶ A)
  (f : A ⟶ E) (hf : f ≫ p = b)

/-- 指定境界を固定する全持ち上げ族を、元の実相対関手空間へ含める全射。 -/
def relativeLiftFixedBoundaryInclusion :
    relativeLiftFixedBoundary p b i f hf ⟶ relativeFunctorSpace p b :=
  vertexFiberι (relativeFunctorPre p b i)
    (relativeFunctorVertex p (i ≫ b) (i ≫ f) (by rw [Category.assoc, hf]))

/-- 全普遍族の指定境界への制限は、元の同じ制限に全次数で定値。 -/
lemma relativeLiftFixedBoundaryInclusion_pre : relativeLiftFixedBoundaryInclusion p b i f hf ≫
    relativeFunctorPre p b i =
      SSet.const (relativeFunctorVertex p (i ≫ b) (i ≫ f) (by rw [Category.assoc, hf])) :=
  vertexFiberι_comp _ _

/-- 指定領域の任意の部分領域でも、元の同じ全制限に定値。 -/
lemma relativeLiftFixedBoundaryInclusion_restrict {K : SSet.{u}} (k : K ⟶ T) :
    relativeLiftFixedBoundaryInclusion p b i f hf ≫ relativeFunctorPre p b (k ≫ i) =
      SSet.const (relativeFunctorVertex p ((k ≫ i) ≫ b) ((k ≫ i) ≫ f)
        (by rw [Category.assoc, hf])) := by
  have h : relativeLiftFixedBoundaryInclusion p b i f hf ≫
      relativeFunctorPre p b i ≫ relativeFunctorPre p (i ≫ b) k =
        SSet.const (relativeFunctorVertex p ((k ≫ i) ≫ b) ((k ≫ i) ≫ f)
          (by rw [Category.assoc, hf])) := by
    let v := relativeFunctorVertex p (i ≫ b) (i ≫ f) (by rw [Category.assoc, hf])
    have hv : (relativeFunctorPre p (i ≫ b) k).app (Opposite.op ⦋0⦌) v =
        relativeFunctorVertex p ((k ≫ i) ≫ b) ((k ≫ i) ≫ f)
          (by rw [Category.assoc, hf]) := by
      rw [show v = relativeFunctorVertex p (i ≫ b) (i ≫ f)
        (by rw [Category.assoc, hf]) from rfl, relativeFunctorPre_vertex]
      apply Subtype.ext
      exact congrArg functorVertex (Category.assoc k i f).symm
    calc
      _ = (relativeLiftFixedBoundaryInclusion p b i f hf ≫ relativeFunctorPre p b i) ≫
          relativeFunctorPre p (i ≫ b) k := (Category.assoc _ _ _).symm
      _ = SSet.const v ≫ relativeFunctorPre p (i ≫ b) k :=
        congrArg (fun r => r ≫ relativeFunctorPre p (i ≫ b) k)
          (relativeLiftFixedBoundaryInclusion_pre p b i f hf)
      _ = SSet.const ((relativeFunctorPre p (i ≫ b) k).app (Opposite.op ⦋0⦌) v) :=
        SSet.const_comp _ _
      _ = _ := congrArg (fun s => SSet.const s) hv
  simpa only [relativeFunctorPre_comp] using h

end SerrePositivity.InfinityCategories.F2.Ind

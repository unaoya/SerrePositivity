module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorFiberHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint

/-!
概要：指定点に定値な底上の相対射を、その点の fiber に値を持つ族へ移す。
方針：元の相対評価を同じ fiber へ持ち上げ、元の fiber Hom の作用と厳密に照合する。
規約：全パラメータの射と実頂点を保持。使われ方：局所三角形比較の fiber への作用。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 全相対族の普遍評価をパラメータで制限すると、同じ族の相対 uncurry になる。 -/
lemma relativeFunctorUncurry_id_parameter {A T E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (k : T ⟶ relativeFunctorSpace p a) :
    (A ◁ k) ≫ relativeFunctorUncurry (𝟙 (relativeFunctorSpace p a)) =
      relativeFunctorUncurry k := by
  simpa only [Category.comp_id] using
    (relativeFunctorUncurry_naturality (𝟙 (relativeFunctorSpace p a)) k).symm

/-- 底が指定点に定値な相対族を、同じ点の fiber に値を持つ関手の族へ移す。 -/
def relativeFunctorBaseFiberHom {C E B : SSet.{u}}
    (p : E ⟶ B) (a : C ⟶ B) (b : B _⦋0⦌) (ha : a = SSet.const b) :
    relativeFunctorSpace p a ⟶ (ihom C).obj (vertexFiber p b) :=
  curry (vertexFiberLift p b (relativeFunctorUncurry (𝟙 (relativeFunctorSpace p a))) (by
    rw [relativeFunctorUncurry_projection, ha, SSet.comp_const]))

/-- 底が定値な全族を fiber へ移して含めると、元の相対全族を厳密に回収する。 -/
lemma relativeFunctorBaseFiberHom_uncurry_ι {C E B : SSet.{u}}
    (p : E ⟶ B) (a : C ⟶ B) (b : B _⦋0⦌) (ha : a = SSet.const b) :
    uncurry (relativeFunctorBaseFiberHom p a b ha) ≫ vertexFiberι p b =
      relativeFunctorUncurry (𝟙 (relativeFunctorSpace p a)) := by
  rw [relativeFunctorBaseFiberHom, uncurry_curry, vertexFiberLift_ι]

/-- 元の実際の射の相対頂点は同じ fiber への持ち上げの関手頂点になる。 -/
lemma relativeFunctorBaseFiberHom_vertex {C E B : SSet.{u}}
    (p : E ⟶ B) (a : C ⟶ B) (b : B _⦋0⦌) (ha : a = SSet.const b)
    (f : C ⟶ E) (hf : f ≫ p = a) :
    (relativeFunctorBaseFiberHom p a b ha).app (Opposite.op ⦋0⦌)
      (relativeFunctorVertex p a f hf) = functorVertex (vertexFiberLift p b f (hf.trans ha)) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro c
  apply Subtype.ext
  rfl

/-- 元の fiber Hom の作用は始域 fiber への制限と同じ fiber への持ち上げの合成。 -/
lemma relativeFunctorFiberHom_eq_restrict {A E B : SSet.{u}}
    (a : A ⟶ B) (p : E ⟶ B) (b : B _⦋0⦌) :
    relativeFunctorPre p a (vertexFiberι a b) ≫
      relativeFunctorBaseFiberHom p (vertexFiberι a b ≫ a) b (vertexFiberι_comp a b) =
      relativeFunctorFiberHom a p b := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro c
  apply Subtype.ext
  rfl

/-- 元の底上の実射は、始域 fiber への制限後も同じ fiber 射の関手頂点を与える。 -/
lemma relativeFunctorBaseFiberHom_pre_vertex {A E B : SSet.{u}}
    (a : A ⟶ B) (p : E ⟶ B) (b : B _⦋0⦌) (f : A ⟶ E) (hf : f ≫ p = a) :
    (relativeFunctorBaseFiberHom p (vertexFiberι a b ≫ a) b (vertexFiberι_comp a b)).app _
      ((relativeFunctorPre p a (vertexFiberι a b)).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex p a f hf)) = functorVertex (vertexFiberMap a p f hf b) := by
  change (relativeFunctorPre p a (vertexFiberι a b) ≫
    relativeFunctorBaseFiberHom p (vertexFiberι a b ≫ a) b (vertexFiberι_comp a b)).app _
      (relativeFunctorVertex p a f hf) = _
  rw [relativeFunctorFiberHom_eq_restrict]
  exact relativeFunctorFiberHom_vertex a p b f hf

end SerrePositivity.InfinityCategories.F2

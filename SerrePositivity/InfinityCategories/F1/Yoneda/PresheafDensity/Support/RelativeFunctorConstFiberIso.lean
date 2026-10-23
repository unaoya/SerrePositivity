module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorConstFiber
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChange

/-!
概要：定値の底を持つ相対関手空間は、その fiber への内部 Hom と同型。
方針：既存の比較射の逆を fiber の包含への後合成から構成する。
規約：元の射の fibration 性や値域の Kan 性を要求しない。
使われ方：定値 unstraightening への相対写像空間を全空間からの写像に同定する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：定値の底の相対関手空間と fiber への関手空間の厳密な同型。
方針：fiber の包含で作る逆射と既存の比較射を、評価の普遍性で往復する。
規約：全ての高次パラメータを含む同型。使われ方：coherent な定値図式への変換。 -/
def relativeFunctorConstFiberIso {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    relativeFunctorSpace p (SSet.const b : A ⟶ B) ≅ (ihom A).obj (vertexFiber p b) := by
  let R := relativeFunctorSpace p (SSet.const b : A ⟶ B)
  let Q := (ihom A).obj (vertexFiber p b)
  let H : R ⟶ Q := relativeFunctorConstFiberHom p b
  let V : Q ⟶ R := relativeFunctorCurry
    (uncurry (𝟙 Q) ≫ vertexFiberι p b) (by
      rw [Category.assoc, vertexFiberι_comp, SSet.comp_const, SSet.comp_const])
  have hH : uncurry H ≫ vertexFiberι p b = relativeFunctorUncurry (𝟙 R) := by
    dsimp only [H, relativeFunctorConstFiberHom]
    rw [uncurry_curry, vertexFiberLift_ι]
  have hV : relativeFunctorUncurry V = uncurry (𝟙 Q) ≫ vertexFiberι p b :=
    relativeFunctorUncurry_curry _ _
  refine ⟨H, V, ?_, ?_⟩
  · apply relativeFunctorUncurry_injective p (SSet.const b : A ⟶ B)
    rw [relativeFunctorUncurry_naturality, hV, ← Category.assoc,
      ← uncurry_natural_left, Category.comp_id, hH]
  · apply uncurry_injective
    apply vertexFiber_hom_ext p b
    rw [uncurry_natural_left, Category.assoc, hH,
      ← relativeFunctorUncurry_naturality, Category.comp_id, hV]

/-- 概要：同型の順方向は既存の fiber への比較そのもの。
方針：定義の順方向の射を取る。
規約：既存 API の頂点・パラメータの式を保持。使われ方：元の比較との整合。 -/
lemma relativeFunctorConstFiberIso_hom {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    (relativeFunctorConstFiberIso (A := A) p b).hom = relativeFunctorConstFiberHom p b := rfl

end SerrePositivity.InfinityCategories.F2

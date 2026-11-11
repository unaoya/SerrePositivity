module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.PinchedFrontHom

/-!
# 端点を同定した豊穣 Hom の合成

概要：豊穣関手の Hom の値を固定した dg 対象へ移した後も、合成は標準 AW 合成で計算できる。
方針：三つの対象の等式と豊穣関手の合成保存を各単体で評価する。
規約：AW の第一引数は後の射、第二引数は前の射。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の Path の分解による解像上の評価の自然性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded MonoidalCategory
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

private lemma normalized_comp_transport {A B C x y z : ClosedCategory R D}
    (hx : A = x) (hy : B = y) (hz : C = z) {d : ℕ}
    (P : (SimplicialCategory.sHom A B) _⦋d⦌) (Q : (SimplicialCategory.sHom B C) _⦋d⦌) :
    (eqToHom (congrArg₂ SimplicialCategory.sHom hx hz)).app (Opposite.op ⦋d⦌)
      ((eComp SSet A B C).app _ (P, Q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW
        ((eqToHom (congrArg₂ SimplicialCategory.sHom hy hz)).app (Opposite.op ⦋d⦌) Q)
        ((eqToHom (congrArg₂ SimplicialCategory.sHom hx hy)).app (Opposite.op ⦋d⦌) P) := by
  subst x y z
  rfl

/-- 概要：豊穣関手の合成の値は端点の移送後に標準 AW 合成になる。
方針：合成保存の等式を単体で評価し、三端点の等式を移す。
規約：始域は任意の単体的豊穣圏でよい。
使われ方：Kerodon 2.5.9（Tag 00SC） の定値先頭面の単位による Path の前半の消去。 -/
lemma normalizedHomValue_comp {C : Type w} [EnrichedCategory SSet.{u} C]
    (F : EnrichedFunctor SSet C (ClosedCategory R D)) (a b c : C)
    {x y z : ClosedCategory R D} (hx : F.obj a = x) (hy : F.obj b = y) (hz : F.obj c = z)
    {d : ℕ} (P : (a ⟶[SSet] b) _⦋d⦌) (Q : (b ⟶[SSet] c) _⦋d⦌) :
    (F.map a c ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hx hz)).app (Opposite.op ⦋d⦌)
      ((eComp SSet a b c).app _ (P, Q)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardAW
        ((F.map b c ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hy hz)).app
          (Opposite.op ⦋d⦌) Q)
        ((F.map a b ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hx hy)).app
          (Opposite.op ⦋d⦌) P) := by
  have h : (F.map a c).app (Opposite.op ⦋d⦌) ((eComp SSet a b c).app _ (P, Q)) =
      (eComp SSet (F.obj a) (F.obj b) (F.obj c)).app (Opposite.op ⦋d⦌)
        ((F.map a b).app _ P, (F.map b c).app _ Q) := by
    exact congrArg (fun φ : ((a ⟶[SSet] b) ⊗ (b ⟶[SSet] c)) ⟶
      (F.obj a ⟶[SSet] F.obj c) ↦ φ.app (Opposite.op ⦋d⦌) (P, Q)) (F.map_comp a b c)
  change (eqToHom (congrArg₂ SimplicialCategory.sHom hx hz)).app (Opposite.op ⦋d⦌)
    ((F.map a c).app _ ((eComp SSet a b c).app _ (P, Q))) = _
  rw [h]
  exact normalized_comp_transport hx hy hz _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

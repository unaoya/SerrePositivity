module
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.Opposite
import all Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
概要：単体的対象の交代面複体の反対化を、反対余単体的対象の交代余面複体と比べる。
方針：各次数は恒等射であり、微分の有限交代和を反対化が保つことを使う。
規約：添字を保ち鎖の向きを反転する。正規化や次数の符号反転は行わない。
使われ方：HA 1.2.4、G10 の標準線形重みから積 Tot への同じ成分での比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology Opposite
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type*} [Category* C] [Preadditive C]

/-- 交代面複体の反対化と、反対余単体図式の交代余面複体の指定同型。 -/
def alternatingFaceOppositeIso (W : SimplicialObject C) :
    (AlternatingFaceMapComplex.obj W).op ≅ AlternatingCofaceMapComplex.obj W.rightOp :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro n m hnm
    have hm : n + 1 = m := hnm
    subst m
    erw [Category.id_comp, Category.comp_id]
    change (AlternatingCofaceMapComplex.obj W.rightOp).d n (n+1) =
      ((AlternatingFaceMapComplex.obj W).d (n+1) n).op
    simp only [AlternatingFaceMapComplex.obj, AlternatingCofaceMapComplex.obj,
      ChainComplex.of_d, CochainComplex.of_d, AlternatingFaceMapComplex.objD,
      AlternatingCofaceMapComplex.objD, op_sum, op_zsmul]
    rfl)

/-- 比較の各次数の前向き射は恒等射。 -/
theorem alternatingFaceOppositeIso_hom_f (W : SimplicialObject C) (n : ℕ) :
    (alternatingFaceOppositeIso W).hom.f n = 𝟙 _ := rfl

end SerrePositivity.HomologicalAlgebra

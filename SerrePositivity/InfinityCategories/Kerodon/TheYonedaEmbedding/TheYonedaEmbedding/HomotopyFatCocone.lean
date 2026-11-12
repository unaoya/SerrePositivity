module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoin
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorHomotopy

/-!
概要：定値図式への指定ホモトピーを、同じ図式・頂点の fat join 余錐にする。
方針：円柱に右の一点を補い、二端の厳密な一致で貼り合わせる。
規約：元の円柱全体を保持する。標的の充填性は不要。
使われ方：coherent な変換を native な join 余錐へ移す準備。

対応節は Kerodon 8.3（Tag 03LZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
variable {K X : SSet.{u}} {f : K ⟶ X} {z : X _⦋0⦌}

/-- 概要：指定ホモトピーから元の図式と指定頂点を持つ fat join 余錐を作る。
方針：右の零単体の成分を忘れて円柱を評価し、両端と貼り合わせる。
規約：元のホモトピーの選択を変えない。使われ方：native 余錐への回収の入力。 -/
def homotopyFatCocone (H : SSet.Homotopy f (SSet.const z)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin K Δ[0] ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc f (SSet.yonedaEquiv.symm z) (fst (K ⊗ Δ[1]) Δ[0] ≫ H.h) (by
    rw [← Category.assoc, whiskerRight_fst, Category.assoc, H.h₀]) (by
    rw [← Category.assoc, whiskerRight_fst, Category.assoc, H.h₁,
      SSet.yonedaEquiv_symm_zero, SSet.comp_const, SSet.comp_const])

/-- 概要：fat join 余錐は元の図式を厳密に保つ。
方針：左因子の貼り合わせの式を使う。
規約：図式の全単体で一致。使われ方：元の余錐の固定条件。 -/
lemma homotopyFatCocone_inl (H : SSet.Homotopy f (SSet.const z)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl K Δ[0] ≫ homotopyFatCocone H = f :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc _ _ _ _ _

/-- 概要：fat join 余錐の右因子は指定した頂点。
方針：右因子の貼り合わせの式を使う。
規約：頂点の厳密な同定。使われ方：回収後の native 余錐の頂点。 -/
lemma homotopyFatCocone_inr (H : SSet.Homotopy f (SSet.const z)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr K Δ[0] ≫ homotopyFatCocone H = SSet.yonedaEquiv.symm z :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc _ _ _ _ _

/-- 概要：fat join 余錐の円柱は元の指定ホモトピーの円柱。
方針：円柱への制限の貼り合わせの式を使う。
規約：右の一点を忘れる射だけを挟む。使われ方：全ホモトピーの追跡。 -/
lemma homotopyFatCocone_cylinder (H : SSet.Homotopy f (SSet.const z)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder K Δ[0] ≫ homotopyFatCocone H = fst (K ⊗ Δ[1]) Δ[0] ≫ H.h :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc _ _ _ _ _

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding

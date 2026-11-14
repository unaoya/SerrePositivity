module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedTerms
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeIndex
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.Nerves.DGNerveOppositeSigns
public import SerrePositivity.DifferentialGraded.Module.Basic
/-!
概要：dg nerve の全斉次成分を、Koszul 符号付きで dg 反対模型へ送る。
方針：実頂点集合を反転し、同じ濃度と実端点から同じ次数の成分を回収する。
規約：ここでは微分式を課す前のデータ。使われ方：β5 の反変 Hom の模型比較。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {n : ℕ}
/-- 同じ全成分を反転し、dg 反対圏の単体データを構成する。 -/
def op (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R Dᵒᵖ n where
  obj i := Opposite.op (s.obj i.rev)
  hom I a b k hI ha hb hk := by
    change _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj b.rev) (s.obj a.rev) k
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign I.card •
      s.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) b.rev a.rev k
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha)
        (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk)
/-- 反対模型から同じ濃度の実成分を回収する逆向きデータ操作。 -/
def unop (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R Dᵒᵖ n) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n where
  obj i := (s.obj i.rev).unop
  hom I a b k hI ha hb hk := by
    change _root_.SerrePositivity.DifferentialGraded.GradedHom R (s.obj b.rev) (s.obj a.rev) k
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign I.card •
      s.hom (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse I) b.rev a.rev k
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.two_le_card_reverse hI)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_min hI hb)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_max hI ha)
        (by simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse] using hk)
/-- 同じ全成分を二回反転すると、元の単体データへ厳密に戻る。 -/
@[simp] lemma unop_op (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R D n) : unop (op s) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · funext i
    simp only [unop, op, Fin.rev_rev, Opposite.unop_op]
  · apply Function.hfunext rfl
    intro I I' h
    cases h
    apply Function.hfunext rfl
    intro a a' h
    cases h
    apply Function.hfunext rfl
    intro b b' h
    cases h
    apply Function.hfunext rfl
    intro k k' h
    cases h
    apply Function.hfunext rfl
    intro hI hI' h
    cases h
    apply Function.hfunext rfl
    intro ha ha' h
    cases h
    apply Function.hfunext rfl
    intro hb hb' h
    cases h
    apply Function.hfunext rfl
    intro hk hk' h
    cases h
    dsimp only [unop, op]
    simp only [id_eq, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_reverse, smul_smul, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign_mul_self,
      one_smul]
    exact s.hom_heq_of_indices_degree rfl (Fin.rev_rev a) (Fin.rev_rev b) rfl
/-- 逆方向も、同じ実単体データを厳密に復元する。 -/
@[simp] lemma op_unop (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R Dᵒᵖ n) : op (unop s) = s := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext
  · funext i
    simp only [unop, op, Fin.rev_rev, Opposite.op_unop]
  · apply Function.hfunext rfl
    intro I I' h
    cases h
    apply Function.hfunext rfl
    intro a a' h
    cases h
    apply Function.hfunext rfl
    intro b b' h
    cases h
    apply Function.hfunext rfl
    intro k k' h
    cases h
    apply Function.hfunext rfl
    intro hI hI' h
    cases h
    apply Function.hfunext rfl
    intro ha ha' h
    cases h
    apply Function.hfunext rfl
    intro hb hb' h
    cases h
    apply Function.hfunext rfl
    intro hk hk' h
    cases h
    dsimp only [unop, op]
    simp only [id_eq, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.card_reverse,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveOppositeIndex.reverse_reverse, smul_smul, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.sign_mul_self,
      one_smul]
    exact s.hom_heq_of_indices_degree rfl (Fin.rev_rev a) (Fin.rev_rev b) rfl
end SerrePositivity.InfinityCategories.Project.DerivedCategories

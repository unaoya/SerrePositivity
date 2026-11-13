module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGStrictNatTransWhisker
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGSimplexComponentExt

/-! # 厳密 dg 自然変換の単体と前後合成の一致

概要：自然変換の前後合成は、全二相単体の dg 関手像と厳密に可換する。
方針：対象の相と全斉次写像の比較を単体データの従属外延性へ渡す。
規約：全次元の単体の等式。使われ方：商側への全 prism の自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {B C D E : Type v}
variable [_root_.SerrePositivity.DifferentialGraded.DGCategory A B] [_root_.SerrePositivity.DifferentialGraded.DGCategory A C] [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable {F G : _root_.SerrePositivity.DifferentialGraded.DGFunctor A C D}

/-- 厳密自然変換を後合成して得る単体は、元の単体の dg 関手像そのもの。 -/
lemma dgStrictNatTransPostcomp_simplex (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (Q : DGFunctor A D E)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A C n) (β : Fin (n + 1) →o Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp η Q).simplex s β = (η.simplex s β).map Q := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexData_ext_of_components A E
  · intro a
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp_phase Q (β a) (s.obj a)
  · intro I a b k hI ha hb hk
    have hab : a ≤ b := by
      rw [ha, hb]
      exact (I.isLeast_min' _).2 (I.max'_mem _)
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPostcomp_transition η Q (β a) (β b) (β.monotone hab)
      (s.hom I a b k hI ha hb hk)

/-- 厳密自然変換を前合成して得る単体は、始域の単体を写してから得る単体。 -/
lemma dgStrictNatTransPrecomp_simplex (P : DGFunctor A B C) (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G)
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A B n) (β : Fin (n + 1) →o Fin 2) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp P η).simplex s β = η.simplex (s.map P) β := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexData_ext_of_components A D
  · intro a
    rfl
  · intro I a b k hI ha hb hk
    have hab : a ≤ b := by
      rw [ha, hb]
      exact (I.isLeast_min' _).2 (I.max'_mem _)
    exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTransPrecomp_transition P η (β a) (β b) (β.monotone hab)
      (s.hom I a b k hI ha hb hk))

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.NatTrans

/-! # 関手等式に沿う厳密 dg 自然変換の成分比較

概要：両相の関手等式と閉零成分の異種等式から、全単体の等式を得る。
方針：関手等式を消去し、閉零成分の関数外延性を使う。
規約：関手の型の輸送を明示する。使われ方：自由係数 prism の商比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable {A : Type u} [CommRing A] {C D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A C] [DGCategory A D]
variable {F G F' G' : _root_.SerrePositivity.DifferentialGraded.DGFunctor A C D}

/-- 両相の関手等式と全閉零成分の比較から自然変換を型付きで比較する。 -/
lemma dgStrictNatTrans_hext (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (η' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')
    (hF : F = F') (hG : G = G') (happ : ∀ x, HEq (η.app x) (η'.app x)) : HEq η η' := by
  cases hF
  cases hG
  have ha : η.app = η'.app := funext fun x => eq_of_heq (happ x)
  cases η
  cases η'
  cases ha
  rfl

/-- 両相と成分の比較は、任意の係数と時刻における全単体の一致を与える。 -/
lemma dgStrictNatTrans_simplex_eq_of_components
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (η' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')
    (hF : F = F') (hG : G = G') (happ : ∀ x, HEq (η.app x) (η'.app x))
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A C n) (β : Fin (n + 1) →o Fin 2) :
    η.simplex s β = η'.simplex s β := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStrictNatTrans_hext η η' hF hG happ
  cases hF
  cases hG
  cases h
  rfl

/-- 両相の関手等式と自然変換の異種等式から、全単体の通常の等式を得る。 -/
lemma dgStrictNatTrans_simplex_eq_of_heq
    (η : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F G) (η' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StrictNatTrans F' G')
    (hF : F = F') (hG : G = G') (hη : HEq η η')
    {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A C n) (β : Fin (n + 1) →o Fin 2) :
    η.simplex s β = η'.simplex s β := by
  cases hF
  cases hG
  cases hη
  rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories

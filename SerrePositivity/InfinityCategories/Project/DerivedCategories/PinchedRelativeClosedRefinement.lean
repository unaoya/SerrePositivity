module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedRelativeHomotopyMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPrecompositionNaturality

/-! # 指定商比較の実相対ホモトピーの閉分母細分

概要：元の充填と指定商単体の相対ホモトピーを、一つの追加閉分母で厳密に輸送する。
方針：像の閉前合成で後合成し、両端を自然性と閉分母の合成則で同定する。
規約：輸送する実写像を保持する。使われ方：有限共通分母の繰り返し細分。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [_root_.SerrePositivity.DifferentialGraded.DGCategory A E]
variable [Small.{u} D] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

/-- 閉分母を細分した充填と、同じ指定商単体の合成分母後の像を実相対ホモトピーで比較。 -/
def PinchedRelativeHomotopy.refineClosed {p q x y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A (F.obj x) (F.obj y) n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A q y n)
    (H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedRelativeHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (F.map q y) t)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E
        (q := F.obj q) (x := F.obj x) (y := F.obj y) (F.onClosed.map s)) g)) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedRelativeHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (F.map p y)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D r) t))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E
        (q := F.obj p) (x := F.obj x) (y := F.obj y) (F.onClosed.map (r ≫ s))) g) :=
  (H.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E (q := F.obj p) (x := F.obj q) (y := F.obj y)
    (F.onClosed.map r))).copy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition_naturality A D E F r t).symm (by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedClosedPrecomposition_comp, ← F.onClosed.map_comp])

/-- 細分した実ホモトピーは、元の実写像への像の閉前合成そのもの。 -/
lemma PinchedRelativeHomotopy.refineClosed_h {p q x y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    {n : ℕ} (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A (F.obj x) (F.obj y) n) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearSimplex A q y n)
    (H : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedRelativeHomotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (F.map q y) t)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedLinearSimplexMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E
        (q := F.obj q) (x := F.obj x) (y := F.obj y) (F.onClosed.map s)) g)) :
    (H.refineClosed A D E F r s g t).homotopy.h = H.homotopy.h ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedHomChainMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A E
        (q := F.obj p) (x := F.obj q) (y := F.obj y) (F.onClosed.map r)) := by
  simp only [PinchedRelativeHomotopy.refineClosed, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedRelativeHomotopy.copy_h,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedRelativeHomotopy.map_h]

end SerrePositivity.InfinityCategories.Project.DerivedCategories

module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Diagram.ProjectiveSpan
public import SerrePositivity.HomotopicalAlgebra.Diagram.PushoutComparison
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyColimit

/-! # Homotopy pushouts when one leg is a cofibration

In a left proper combinatorial model category, the actual projective
hocolim comparison for a span is a weak equivalence whenever one fixed
leg is a cofibration. No cofibrancy of its objects is required.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.HomotopyColimit
variable (K : Type w) [SmallCategory K] (e : K ≌ WalkingSpan)
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [(weakEquivalences C).IsStableUnderCobaseChangeAgainst (cofibrations C)]

local instance : HasColimitsOfSize.{w, w} C := Smith.locallyPresentable_hasColimits (C := C)

lemma comparison_weakEquivalence_of_span (D : K ⥤ C)
    (hD : cofibrations C (D.map (e.inverse.map WalkingSpan.Hom.fst))) :
    weakEquivalences C ((comparison K I J).app D) := by
  let R := (replacement K I J).obj D
  let q := (replacementComparison K I J).app D
  have hR := (ProjectiveSpan.legs_cofibrations K e I J R (replacement_isCofibrant K I J D)).1
  have hs := IsPushout.of_isColimit_cocone ((colimit.isColimit R).whiskerEquivalence e.symm)
  have ht := IsPushout.of_isColimit_cocone ((colimit.isColimit D).whiskerEquivalence e.symm)
  exact weakEquivalence_of_pushout_comparison hs ht
    (q.app (e.inverse.obj WalkingSpan.zero))
    (q.app (e.inverse.obj WalkingSpan.left))
    (q.app (e.inverse.obj WalkingSpan.right)) ((comparison K I J).app D) hR hD
    (replacementComparison_objectwiseWeakEquivalence K I J D _)
    (replacementComparison_objectwiseWeakEquivalence K I J D _)
    (replacementComparison_objectwiseWeakEquivalence K I J D _)
    (q.naturality _) (q.naturality _)
    (colimit.ι_map q _) (colimit.ι_map q _)

end SerrePositivity.DiagramModel.HomotopyColimit

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.2.4.4" (partial := stronger-hyp) "仮定：左固有モデル圏 C、span の一辺が cofibration に加え IsLocallyPresentable と小さい cofibrant generators I,J（Lean が強い）。結論：実際の projective homotopy-colimit comparison が元の pushout への弱同値で、原典の (ii) の場合の homotopy pushout と一致。(i) の一般の cofibrant objects 版と非 combinatorial の C は含まない。"] _root_.SerrePositivity.DiagramModel.HomotopyColimit.comparison_weakEquivalence_of_span

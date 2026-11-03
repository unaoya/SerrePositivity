module

public import SerrePositivity.InfinityCategories.F2.Compact.Definition
public import SerrePositivity.InfinityCategories.F1.SquareFunctorTransport

/-!
概要：κ-filtered 余極限保存の全自然同型不変性と、一つの余極限余錐による判定。
方針：元の全余錐の関手同型で普遍性を移す。
規約：余極限が存在しない図式に、選択した余錐を要求しない。
使われ方：Map(x,−) の具体的模型による κ-compact 性の証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {κ : Cardinal.{u}} {C : SSet.{max u v}} {Y : SSet.{max u v + 1}}
  [Quasicategory Y]
  {F G : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶ Y}

/-- 元の全自然同型で比較される関手は、同じ κ-filtered 余極限保存性を持つ。 -/
lemma PreservesKappaFilteredColimits.of_functorIso
    (h : PreservesKappaFilteredColimits.{u, v} κ F) (e : FunctorIso F G) :
    PreservesKappaFilteredColimits.{u, v} κ G := by
  intro I hI hFiltered D c hc
  exact (h I D c hc).of_functorIso (e.precomp (JoinCocone.ulift c).val)

/-- 元の各図式の、一つの全余極限余錐の像だけを調べれば保存性を判定できる。 -/
lemma preservesKappaFilteredColimits_of_exists [Quasicategory C]
    (h : ∀ (I : SSet.{u}) [Quasicategory I] [IsKappaFiltered κ I]
      (D : (SSet.uliftFunctor.{v, u}).obj I ⟶ C), HasColimit D →
        ∃ c : JoinCocone D, IsColimitCone c ∧
          IsColimitCone (mapJoinCocone F (JoinCocone.ulift c))) :
    PreservesKappaFilteredColimits.{u, v} κ F := by
  intro I hI hFiltered D c hc
  obtain ⟨d, hd, hFd⟩ := h I D ⟨c, hc⟩
  let c' := JoinCocone.ulift.{max u v, max u v + 1} c
  let d' := JoinCocone.ulift.{max u v, max u v + 1} d
  have hc' : IsColimitCone c' := (isColimitCone_iff_ulift c).mp hc
  have hd' : IsColimitCone d' := (isColimitCone_iff_ulift d).mp hd
  exact hFd.of_functorIso
    ((coconeFunctorIsoOfVertexIso d' c' (colimitConeIso d' c' hd' hc')).postcomp F)

/-- κ-compact 性も、存在する各図式の一つの元の余極限余錐で判定できる。 -/
lemma isKappaCompact_of_exists [Quasicategory C] {x : C _⦋0⦌}
    (h : ∀ (I : SSet.{u}) [Quasicategory I] [IsKappaFiltered κ I]
      (D : (SSet.uliftFunctor.{v, u}).obj I ⟶ C), HasColimit D →
        ∃ c : JoinCocone D, IsColimitCone c ∧ IsColimitCone
          (mapJoinCocone (covariantRepresentableInfinity x) (JoinCocone.ulift c))) :
    IsKappaCompact.{u, v} κ x :=
  preservesKappaFilteredColimits_of_exists h

end SerrePositivity.InfinityCategories.F2.Compact

module

public import SerrePositivity.InfinityCategories.F1B.Cones.CoconeFamilyEquivalenceLifting
public import SerrePositivity.InfinityCategories.F1B.Fibrations.VertexIsoLifting
public import SerrePositivity.InfinityCategories.F1B.KanExtension.RelativeColimitFunctorIso

/-!
概要：図式固定の底余錐の同型に沿って相対余極限を移す。
方針：余錐の族の同型を持ち上げ、余錐全体の同型による相対余極限の保存を使う。
規約：元の図式と新しい像の余錐は厳密に保つ。
使われ方：標準底余錐上の局所存在を普遍 comma 底余錐上の局所存在へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F1B

/-- 概要：像の余錐と同型な指定底余錐の上にも相対余極限がある。
方針：固定図式の余錐の族の後合成で同型を持ち上げ、相対普遍性を移す。
規約：同型は図式固定の余錐の族の中で指定する。
使われ方：底余錐を標準形と普遍 comma 形の間で取り替える。 -/
lemma exists_kanRelativeColimit_over_iso_image {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (p : K ⟶ D) (U : D ⟶ E)
    (hU : SerrePositivity.InfinityCategories.F1B.EquivalenceLifting U) (c : JoinCocone p) (hc : IsRelativeColimitCone U c)
    (b : JoinCocone (p ≫ U))
    (e : VertexIso (coconeFamilyVertexEquiv (p ≫ U) b)
      (coconeFamilyVertexEquiv (p ≫ U) (kanPostcomposeCocone U c))) :
    ∃ d : JoinCocone p, IsRelativeColimitCone U d ∧ d.val ≫ U = b.val := by
  have : InnerFibration U := hU.innerFibration
  let q := kanCoconeFamilyPostcomp p U
  have he : VertexIso (coconeFamilyVertexEquiv (p ≫ U) b)
      (q.app (Opposite.op ⦋0⦌) (coconeFamilyVertexEquiv p c)) := by
    rw [kanCoconeFamilyPostcomp_vertex]
    exact e
  obtain ⟨v, hv, ⟨ev⟩⟩ := exists_kanVertexIso_lift_target q
    (SerrePositivity.InfinityCategories.F1B.coconeFamilyPostcomp_equivalenceLifting p U hU) (coconeFamilyVertexEquiv p c)
    (coconeFamilyVertexEquiv (p ≫ U) b) he
  obtain ⟨d, rfl⟩ := (coconeFamilyVertexEquiv p).surjective v
  have hv' : kanPostcomposeCocone U d = b := by
    apply (coconeFamilyVertexEquiv (p ≫ U)).injective
    rw [← kanCoconeFamilyPostcomp_vertex]
    exact hv
  have ei : FunctorIso d.val c.val :=
    VertexIso.map ev (vertexFiberι (coconeRestriction K D) (functorVertex p))
  exact ⟨d, kanIsRelativeColimitCone_of_functorIso U hc ei.symm,
    congrArg Subtype.val hv'⟩

end SerrePositivity.InfinityCategories.F1B

module

public import SerrePositivity.InfinityCategories.F2.Idempotent.EssentialImageLift
public import SerrePositivity.InfinityCategories.Core.FunctorIsoTransport

/-!
概要：元の充満忠実な関手の本質像内に値を持つ全図式を、元の始域の全図式へ戻す。
方針：元の図式を頂点条件で全部分圏へ因子化し、元の本質像同値の逆を合成する。
規約：比較は全図式の可逆二胞体。添字の quasicategory 性は不要。
使われ方：前層を介した元の関手の延長を冪等完備な標的へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 全頂点が元の本質像内にある図式は、元の始域の全図式として全自然同型まで回収できる。 -/
lemma exists_diagram_in_fullyFaithful_source {K X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (f : X ⟶ Y) (hf : IsFullyFaithful f)
    (g : K ⟶ Y) (hg : ∀ k : K _⦋0⦌, ∃ x : X _⦋0⦌,
      Nonempty (VertexIso (f.app (Opposite.op ⦋0⦌) x) (g.app (Opposite.op ⦋0⦌) k))) :
    ∃ F : K ⟶ X, Nonempty (FunctorIso (F ≫ f) g) := by
  let g' : K ⟶ fullEssentialImage f := fullSubcomplexLift
    (fun y ↦ ∃ x, Nonempty (VertexIso (f.app (Opposite.op ⦋0⦌) x) y)) g hg
  let e := essentialImageEquivalence f hf
  have hfac : e.hom ≫ (fullEssentialImage f).ι = f := essentialImageLift_inclusion f
  have h : g' ≫ (fullEssentialImage f).ι = g := fullSubcomplexLift_ι _ _ _
  refine ⟨g' ≫ e.inv, ⟨?_⟩⟩
  have k : FunctorIso (((g' ≫ e.inv) ≫ e.hom) ≫ (fullEssentialImage f).ι)
      (g' ≫ (fullEssentialImage f).ι) := by
    simpa only [Category.assoc, Category.comp_id] using
      (e.invHomIso.precomp g').postcomp (fullEssentialImage f).ι
  exact functorIsoOfEq k
    ((Category.assoc _ _ _).trans (congrArg ((g' ≫ e.inv) ≫ ·) hfac)) h

end SerrePositivity.InfinityCategories.F2.Idempotent

module
public import SerrePositivity.InfinityCategories.Derived.DGKernelHomotopyAdjunction
/-!
概要：通常の h の同じ余単位を実辺で表し、その全入力に対する普遍性を回収する。
方針：右随伴の値を実頂点に戻し、辺の類の全射性と同じ随伴の Hom 同値を使う。
規約：写像空間全体の普遍性は別工程。使われ方：一般 RHom の実右随伴の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
open scoped Simplicial
/-- 同じ実余単位への後合成は、全入力の通常の h の Hom 集合の全単射。 -/
lemma dgKernelCounitEdge_exists (P : Bimodule R E D)
    (y : dgModuleDerivedInfinityCategory R E _⦋0⦌) :
    ∃ (x : dgModuleDerivedInfinityCategory R D _⦋0⦌)
      (e : Truncated.Edge (X := (truncation 2).obj (dgModuleDerivedInfinityCategory R E))
        ((dgKernelDerivedInfinity R D E P).app (Opposite.op ⦋0⦌) x) y),
      ∀ z : dgModuleDerivedInfinityCategory R D _⦋0⦌,
        Function.Bijective (fun f : HomotopyCategory.mk z ⟶ HomotopyCategory.mk x =>
          (hoFunctor.map (dgKernelDerivedInfinity R D E P)).toFunctor.map f ≫
            Truncated.HomotopyCategory.homMk e) := by
  let adj := dgKernelHomotopyAdjunction R D E P
  let G := dgKernelHomotopyRightAdjoint R D E P
  let F := (hoFunctor.map (dgKernelDerivedInfinity R D E P)).toFunctor
  let x := HomotopyCategory.objEquiv (G.obj (HomotopyCategory.mk y))
  have hx : HomotopyCategory.mk x = G.obj (HomotopyCategory.mk y) :=
    HomotopyCategory.objEquiv.left_inv _
  let t := eqToIso hx
  let ε := F.map t.hom ≫ adj.counit.app (HomotopyCategory.mk y)
  obtain ⟨e, he⟩ := homotopyCategory_homMk_surjective
    ((dgKernelDerivedInfinity R D E P).app (Opposite.op ⦋0⦌) x) y ε
  refine ⟨x, e, fun z => ?_⟩
  let ev : (HomotopyCategory.mk z ⟶ HomotopyCategory.mk x) ≃
      (F.obj (HomotopyCategory.mk z) ⟶ HomotopyCategory.mk y) :=
    (Iso.homCongr (Iso.refl _) t).trans (adj.homEquiv _ _).symm
  have hev : (ev : _ → _) =
      (fun f : HomotopyCategory.mk z ⟶ HomotopyCategory.mk x =>
        F.map f ≫ Truncated.HomotopyCategory.homMk e) := by
    funext f
    change (adj.homEquiv _ _).symm ((𝟙 _) ≫ f ≫ t.hom) = _
    rw [Category.id_comp]
    rw [Adjunction.homEquiv_counit, F.map_comp, Category.assoc, he]
  rw [← hev]
  exact ev.bijective
end SerrePositivity.InfinityCategories

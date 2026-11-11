module
public import SerrePositivity.KST.SConstruction.PerfectDGStableModel
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.FullInclusionLift
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元三辺が実 Perf 内にある全合成二単体を、元全図式ごと実 Perf 内へ持ち上げる。
方針：D 正本の全頂点による充満部分圏持ち上げと包含の単射性を使用する。
規約：元二単体・三つの元円柱を厳密に回収し、別の二単体を選ばない。
使われ方：元実逆回転の上指定二単体を二段 Perf 評価・固定 ν へ運ぶ。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed DifferentialGraded InfinityCategories SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
local notation "I" => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (perfectDGModuleInclusion R E Set.univ)

/-- 概要：元 Perf 三辺を持つ全二単体を元全包含の厳密な逆像にする。
方針：元二単体の全頂点を元二側面から回収し、充満包含で全境界を反映する。
規約：同じ全二単体と元三円柱を保持。使われ方：元上二単体の同じ Perf 持ち上げ。 -/
lemma exists_perfectFunctorCompositionTriangle
    {A : SSet.{max (u + 1) v}} {f g h : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R E)}
    (l : SSet.Homotopy f g) (r : SSet.Homotopy g h) (d : SSet.Homotopy f h)
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp l (I))
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp r (I)) (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d (I))) :
    ∃ U : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d,
      U.diagram ≫ (ihom A).map (I) = T.diagram := by
  letI : Mono (I) := by
    change Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgFullSubcategoryInclusion R (RightModule R E)
      (modulePerfectProjectiveOver R E Set.univ)))
    infer_instance
  have h2 : (A ◁ stdSimplex.δ (2 : Fin 3)) ≫ uncurry T.diagram = l.h ≫ (I) :=
    (uncurry_natural_left (stdSimplex.δ (2 : Fin 3)) T.diagram).symm.trans
      ((congrArg uncurry T.face_two).trans (uncurry_curry _))
  have h0 : (A ◁ stdSimplex.δ (0 : Fin 3)) ≫ uncurry T.diagram = r.h ≫ (I) :=
    (uncurry_natural_left (stdSimplex.δ (0 : Fin 3)) T.diagram).symm.trans
      ((congrArg uncurry T.face_zero).trans (uncurry_curry _))
  have hv : ∀ z : (A ⊗ (Δ[2] : SSet.{max (u + 1) v})) _⦋0⦌,
      modulePerfectProjectiveOver R E Set.univ (((uncurry T.diagram).app _ z).obj 0) := by
    rintro ⟨a, t⟩
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
    fin_cases i
    · have he := congrArg (fun m =>
        (m.app (Opposite.op ⦋0⦌) (a, stdSimplex.obj₀Equiv.symm (0 : Fin 2))).obj 0) h2
      change ((uncurry T.diagram).app _ (a, stdSimplex.obj₀Equiv.symm (0 : Fin 3))).obj 0 =
        ((l.h.app _ (a, stdSimplex.obj₀Equiv.symm (0 : Fin 2))).obj 0).val at he
      exact he.symm ▸ ((l.h.app _ (a, stdSimplex.obj₀Equiv.symm (0 : Fin 2))).obj 0).property
    · have he := congrArg (fun m =>
        (m.app (Opposite.op ⦋0⦌) (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0) h2
      change ((uncurry T.diagram).app _ (a, stdSimplex.obj₀Equiv.symm (1 : Fin 3))).obj 0 =
        ((l.h.app _ (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0).val at he
      exact he.symm ▸ ((l.h.app _ (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0).property
    · have he := congrArg (fun m =>
        (m.app (Opposite.op ⦋0⦌) (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0) h0
      change ((uncurry T.diagram).app _ (a, stdSimplex.obj₀Equiv.symm (2 : Fin 3))).obj 0 =
        ((r.h.app _ (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0).val at he
      exact he.symm ▸ ((r.h.app _ (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0).property
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift R (RightModule R E) (modulePerfectProjectiveOver R E Set.univ)
    (uncurry T.diagram) hv
  have hF : F ≫ (I) = uncurry T.diagram :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.fullInclusionLift_comp R (RightModule R E) (modulePerfectProjectiveOver R E Set.univ)
      (uncurry T.diagram) hv
  let diag := curry F
  have hd : diag ≫ (ihom A).map (I) = T.diagram := by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, hF]
  have fac (i : Fin 3) {f' g' : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PerfectDGModule R E)}
      (q : SSet.Homotopy f' g')
      (hq : stdSimplex.δ i ≫ T.diagram = curry (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp q (I)).h) :
      stdSimplex.δ i ≫ diag = curry q.h := by
    apply uncurry_injective
    apply (cancel_mono (I)).1
    calc
      uncurry (stdSimplex.δ i ≫ diag) ≫ (I) =
          uncurry ((stdSimplex.δ i ≫ diag) ≫ (ihom A).map (I)) :=
        (uncurry_natural_right _ (I)).symm
      _ = uncurry (stdSimplex.δ i ≫ (diag ≫ (ihom A).map (I))) :=
        congrArg uncurry (Category.assoc _ _ _)
      _ = uncurry (stdSimplex.δ i ≫ T.diagram) :=
        congrArg (fun m => uncurry (stdSimplex.δ i ≫ m)) hd
      _ = uncurry (curry (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp q (I)).h) := congrArg uncurry hq
      _ = uncurry (curry q.h) ≫ (I) := by rw [uncurry_curry, uncurry_curry]; rfl
  refine ⟨{ diagram := diag, face_zero := ?_, face_one := ?_, face_two := ?_ }, hd⟩
  · exact fac 0 r T.face_zero
  · exact fac 1 d T.face_one
  · exact fac 2 l T.face_two
/-- 概要：実合成二単体の全頂点は元三関手の対象像に入る。
方針：元二側面と元円柱の端点等式で対象を回収する。
規約：全二単体を変更しない。使われ方：元上二単体の実 Perf 頂点判定。 -/
lemma perfectFunctorCompositionTriangle_vertices
    {A : SSet.{max (u + 1) v}} {f g h : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (RightModule R E)}
    {l : SSet.Homotopy f g} {r : SSet.Homotopy g h} {d : SSet.Homotopy f h}
    (T : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d)
    (hf : ∀ a : A _⦋0⦌, modulePerfectProjectiveOver R E Set.univ ((f.app _ a).obj 0))
    (hg : ∀ a : A _⦋0⦌, modulePerfectProjectiveOver R E Set.univ ((g.app _ a).obj 0))
    (hh : ∀ a : A _⦋0⦌, modulePerfectProjectiveOver R E Set.univ ((h.app _ a).obj 0)) :
    ∀ z : (A ⊗ (Δ[2] : SSet.{max (u + 1) v})) _⦋0⦌,
      modulePerfectProjectiveOver R E Set.univ (((uncurry T.diagram).app _ z).obj 0) := by
  have h2 : (A ◁ stdSimplex.δ (2 : Fin 3)) ≫ uncurry T.diagram = l.h :=
    (uncurry_natural_left (stdSimplex.δ (2 : Fin 3)) T.diagram).symm.trans
      ((congrArg uncurry T.face_two).trans (uncurry_curry _))
  have h0 : (A ◁ stdSimplex.δ (0 : Fin 3)) ≫ uncurry T.diagram = r.h :=
    (uncurry_natural_left (stdSimplex.δ (0 : Fin 3)) T.diagram).symm.trans
      ((congrArg uncurry T.face_zero).trans (uncurry_curry _))
  rintro ⟨a, t⟩
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective t
  fin_cases i
  · have he := congrArg (fun m =>
        (m.app (Opposite.op ⦋0⦌) (a, stdSimplex.obj₀Equiv.symm (0 : Fin 2))).obj 0) h2
    change ((uncurry T.diagram).app _ (a, stdSimplex.obj₀Equiv.symm (0 : Fin 3))).obj 0 =
      ((l.h.app _ (a, stdSimplex.obj₀Equiv.symm (0 : Fin 2))).obj 0) at he
    have hv := congrArg (fun m => (m.app (Opposite.op ⦋0⦌) a).obj 0) l.h₀
    change ((l.h.app _ (a, stdSimplex.obj₀Equiv.symm (0 : Fin 2))).obj 0) = _ at hv
    exact (he.trans hv).symm ▸ hf a
  · have he := congrArg (fun m =>
        (m.app (Opposite.op ⦋0⦌) (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0) h2
    change ((uncurry T.diagram).app _ (a, stdSimplex.obj₀Equiv.symm (1 : Fin 3))).obj 0 =
      ((l.h.app _ (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0) at he
    have hv := congrArg (fun m => (m.app (Opposite.op ⦋0⦌) a).obj 0) l.h₁
    change ((l.h.app _ (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0) = _ at hv
    exact (he.trans hv).symm ▸ hg a
  · have he := congrArg (fun m =>
        (m.app (Opposite.op ⦋0⦌) (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0) h0
    change ((uncurry T.diagram).app _ (a, stdSimplex.obj₀Equiv.symm (2 : Fin 3))).obj 0 =
      ((r.h.app _ (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0) at he
    have hv := congrArg (fun m => (m.app (Opposite.op ⦋0⦌) a).obj 0) r.h₁
    change ((r.h.app _ (a, stdSimplex.obj₀Equiv.symm (1 : Fin 2))).obj 0) = _ at hv
    exact (he.trans hv).symm ▸ hh a
end SerrePositivity.KST.SConstruction

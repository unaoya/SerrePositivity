module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorRightAxisInverseRotationYoneda
public import SerrePositivity.KST.SConstruction.DGOdotMilnorFlatKernelNullSquare
public import SerrePositivity.DifferentialGraded.Bimodule.Right
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalTransport

/-!
概要：実第二 graph の厚核制限を同じ加群として保持し、各対象の収縮を証明する。
方針：保存済みの全 Yoneda 比較から零頂点性を移し、実収縮元を回収する。
規約：対象別の収縮から全 Hom end の自然な収縮や h-射影性を結論しない。
使われ方：D の自然収縮判定に代入する固定模型と対象別条件の準備。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
private lemma contractibleOfComparison {A : Type u} [CommRing A]
    {C E : Type v} [DGCategory A C] [DGCategory A E]
    (F G : DGFunctor A C E) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map F) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map G))
    (x : C) (hG : ∃ h : GradedHom A (G.obj x) (G.obj x) (-1),
      (homObject A E (G.obj x) (G.obj x)).d (-1) 0 h = (unitElement A (G.obj x)).val) :
    ∃ h : GradedHom A (F.obj x) (F.obj x) (-1),
      (homObject A E (F.obj x) (F.obj x)).d (-1) 0 h = (unitElement A (F.obj x)).val := by
  obtain ⟨h, dh⟩ := hG
  have hy := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_contractingElement_isZeroVertex _ h dh
  have ex := e.app (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at ex
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_exists_contractingElement_of_isTerminalVertex _ (hy.2.of_vertexIso ex.symm)

private lemma mapContractible {A : Type u} [CommRing A]
    {C : Type v} {E : Type w} [DGCategory A C] [DGCategory A E]
    (F : DGFunctor A C E) (x : C)
    (hx : ∃ h : GradedHom A x x (-1),
      (homObject A C x x).d (-1) 0 h = (unitElement A x).val) :
    ∃ h : GradedHom A (F.obj x) (F.obj x) (-1),
      (homObject A E (F.obj x) (F.obj x)).d (-1) 0 h = (unitElement A (F.obj x)).val := by
  obtain ⟨h, dh⟩ := hx
  exact ⟨(F.map x x).f (-1) h, F.map_contractingElement A x h dh⟩

variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "B" => DGOdotGluing R d
local notation "P" => DGCategoryCellResolution.Source R (B)
local notation "I" => dgQuotientImage R (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R (B) (I)
local notation "Q" => DGQuotient.QuotientObject (P) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (B) (I))
local notation "k" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernelInclusion R (B) (I)
local notation "q" => dgOdotMilnorResolvedInclusion R d
local notation "G" => dgOdotMilnorRightAxisQuotientTarget R d

/-- 概要：実第二 graph を同じ厚核へ制限した加群値関手 Γ。
方針：元 Perf 対象の同じ全 Hom を使用。
規約：Yoneda で置換しない。使われ方：自然収縮の固定対象。 -/
def dgOdotMilnorKernelTargetFamily : DGFunctor R (K) (RightModule R (Q)) :=
  dgPerfectModuleUnderlying R (Q) ((k).comp (G))

/-- 概要：Γ を積 dg 圏上の右加群として表示する。
方針：全二作用を保持する既存の圏同値の逆像を取る。
規約：この表示だけで h-射影性を主張しない。使われ方：D の一般判定の入力。 -/
def dgOdotMilnorKernelTargetProductModule :
    ModuleCategory R (DGTensorCategory R (Q)ᵒᵖ (K))ᵒᵖ :=
  (rightModuleBimoduleEquivalence R (Q) (K)).inverse.obj
    (BimoduleCategory.of R (Q) (K) (dgOdotMilnorKernelTargetFamily R d))

/-- 概要：積加群表示を戻すと元の Γ を両作用ごと回収する。
方針：既存の圏同値の余単位を使用。
規約：新しい graph を選ばない。使われ方：D の入力表示との照合。 -/
def dgOdotMilnorKernelTargetProductRecovery :
    (rightModuleBimoduleEquivalence R (Q) (K)).functor.obj
      (dgOdotMilnorKernelTargetProductModule R d) ≅
        BimoduleCategory.of R (Q) (K) (dgOdotMilnorKernelTargetFamily R d) :=
  (rightModuleBimoduleEquivalence R (Q) (K)).counitIso.app _

/-- 概要：Γ の各右加群値は h-射影的。
方針：同じ元 Perf 値の定義から証拠を取り出す。
規約：積 dg 圏上の h-射影性とは区別。使われ方：自然収縮の条件照合。 -/
lemma dgOdotMilnorKernelTarget_objectwise_projective (x : K) :
    moduleHomotopicallyProjective R (Q)
      (ForgetEnrichment.of (Complex R) ((dgOdotMilnorKernelTargetFamily R d).obj x)) :=
  (((k).comp (G)).obj x).property.1

/-- 概要：元第二 graph の厚核制限と同じ商 Yoneda の全比較。
方針：同じ実逆回転の二つの保存済み全比較を合成して制限する。
規約：厳密 dg 自然同型と同一視しない。使われ方：各対象の零性の移送。 -/
def dgOdotMilnorKernelTargetYonedaComparison :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorKernelTargetFamily R d))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((k).comp ((q).comp (dgYoneda R (Q))))) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
    ((dgOdotMilnorRightAxisInverseRotationRealizedNerveComparison R d).symm.trans
      (dgOdotMilnorRightAxisInverseRotationYonedaComparison R d)) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (k))
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (k) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgPerfectModuleUnderlying R (Q) (G)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotMilnorKernelTargetFamily R d) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ _).symm
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e ha (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp _ _).symm

/-- 概要：Γ の各対象には実加群 Hom の収縮元がある。
方針：同じ商 ε の零頂点性を全比較の成分で移す。
規約：収縮の核方向の自然性は未主張。使われ方：D の対象別可縮条件。 -/
lemma dgOdotMilnorKernelTarget_objectwise_contractible (x : K) :
    ∃ h : GradedHom R ((dgOdotMilnorKernelTargetFamily R d).obj x)
      ((dgOdotMilnorKernelTargetFamily R d).obj x) (-1),
      (homObject R (RightModule R (Q)) ((dgOdotMilnorKernelTargetFamily R d).obj x)
        ((dgOdotMilnorKernelTargetFamily R d).obj x)).d (-1) 0 h =
          (unitElement R ((dgOdotMilnorKernelTargetFamily R d).obj x)).val := by
  have hc := dgOdotMilnorFlatKernelImage_contractible R d x
  have hy := mapContractible (dgYoneda R (Q)) _ hc
  exact contractibleOfComparison _ _ (dgOdotMilnorKernelTargetYonedaComparison R d) x hy

end SerrePositivity.KST.SConstruction

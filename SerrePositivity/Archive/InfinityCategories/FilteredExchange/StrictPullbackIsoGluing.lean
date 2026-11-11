module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.StrictPullbackHomotopyGluing
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.HomotopyIsoTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerHom
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanHomotopyEquivalence

/-!
概要：共通の底で整合する指定二脚の関手同型を、厳密な引き戻し全体へ貼り合わせる。
方針：両端の式を引き戻し条件から明示し、同じ類の代表を厳密に揃える。
規約：二脚の同型の存在だけでは結論しない。使われ方：実模型比較全体の同値性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2
variable {T L M R : SSet.{u}} (p : L ⟶ M) (q : R ⟶ M)
  (a b : T ⟶ pullback p q)

/-- 両脚の像の端点の等式は、元の厳密な引き戻し条件から得る。 -/
lemma strictPullbackImage_eq (k : T ⟶ pullback p q) :
    (k ≫ pullback.snd p q) ≫ q = (k ≫ pullback.fst p q) ≫ p := by
  simp only [Category.assoc, pullback.condition]

/-- 指定同型の代表を後合成した円柱の類は、同じ指定同型の後合成の射である。 -/
lemma functorIsoRepresentative_postcomp_hom
    [Quasicategory L] [Quasicategory M] {f g : T ⟶ L} (e : FunctorIso f g) :
    (e.postcomp p).hom = SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp e.simplicialHomotopy p)) := by
  rw [functorIso_postcomp_hom, functorHomotopyPostcomp_hom,
    SerrePositivity.InfinityCategories.functorIso_simplicialHomotopy_hom]
  rfl

/-- 共通の底で同じ指定像を持つ二脚の同型は、全体の関手同型へ貼り合わせられる。 -/
lemma strictPullback_functorIso_exists [KanComplex L] [KanComplex M] [KanComplex R]
    [InnerFibration p] [KanComplex (pullback p q)]
    (e : FunctorIso (a ≫ pullback.fst p q) (b ≫ pullback.fst p q))
    (d : FunctorIso (a ≫ pullback.snd p q) (b ≫ pullback.snd p q))
    (h : HEq (e.postcomp p) (d.postcomp q)) : Nonempty (FunctorIso a b) := by
  let H := e.simplicialHomotopy
  let K := d.simplicialHomotopy
  let D := strictPullbackRightHomotopyBase p q a b K
  have hd : functorIsoOfEq (d.postcomp q) (strictPullbackImage_eq p q a)
      (strictPullbackImage_eq p q b) = functorIsoOfSimplicialHomotopy D := by
    exact functorIsoOfEq_of_homotopy_h_eq (functorHomotopyPostcomp K q) D
      (d.postcomp q) _ (functorIsoRepresentative_postcomp_hom q d) rfl _ _ rfl
  have he : functorIsoOfEq (d.postcomp q) (strictPullbackImage_eq p q a)
      (strictPullbackImage_eq p q b) = e.postcomp p :=
    eq_of_heq ((functorIsoOfEq_heq _ _ _).trans h.symm)
  have hh : SSet.Truncated.HomotopyCategory.homMk
      (functorEdgeOfSimplicialHomotopy (functorHomotopyPostcomp H p)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy D) := by
    exact (functorIsoRepresentative_postcomp_hom p e).symm.trans
      (congrArg (fun z => z.hom) (he.symm.trans hd))
  obtain ⟨V, _⟩ := strictPullback_exists_homotopy p q a b H K hh
  exact ⟨functorIsoOfSimplicialHomotopy V⟩

end SerrePositivity.InfinityCategories.F2

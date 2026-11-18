module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorBaseChangeVertices
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.DiagramIsoNormalizationAlgebra
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.RelativeFunctorVertexIsoProjection
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerComposition
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorPrismEdgeLifting
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport

/-!
概要：相対関手空間の同じ指定同型を、前合成と端点の等式で移したときの射影を計算する。
方針：元の相対同型の射影公式を再利用し、等式から来る同型の前合成を計算する。
規約：HTT §3.3.2・Kerodon §5.6（Tag 028T）の構成に付随する、相対関手模型の特殊な法則。
  相対同型を選び直さず、元の指定成分そのものを保持する。
使われ方：P3-C1PS、scaffold上のpointed比較の両端を固定する計算。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 関手の等式から来る同じ同型の前合成は、前合成した等式の同型。 -/
lemma functorIsoEq_precomp {A D X : SSet.{u}} {f g : A ⟶ X}
    (h : f = g) (i : D ⟶ A) :
    FunctorIso.precomp (eqToIso (congrArg (fun k => HomotopyCategory.mk (functorVertex k)) h)) i =
      eqToIso (congrArg (fun k => HomotopyCategory.mk (functorVertex k))
        (congrArg (fun k => i ≫ k) h)) := by
  cases h
  simp only [eqToIso_refl, functorIso_precomp_eq_mapIso, Functor.mapIso_refl]
  rfl

/-- 元の相対同型の前合成と端点移送の後でも、射影は同じ端点等式の同型。
HTT §3.3.2・Kerodon Tag 028Tの構成の、この相対関手模型での特殊な計算法則。 -/
@[cite HTT "3.3.2" (partial := special) "相対関手模型の指定同型の前合成と端点移送の射影公式。"]
lemma relativeFunctorVertexIsoImage_transport_projection
    {A D E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B)
    (f g : A ⟶ E) (hf : f ≫ p = a) (hg : g ≫ p = a)
    (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg))
    (i : D ⟶ A) {f' g' : D ⟶ E} (hf' : i ≫ f = f') (hg' : i ≫ g = g')
    (hp : f' ≫ p = g' ≫ p) :
    (functorIsoOfEq ((relativeFunctorVertexIsoImage p a f g hf hg e).precomp i) hf' hg').postcomp p =
      eqToIso (congrArg (fun k => HomotopyCategory.mk (functorVertex k)) hp) := by
  subst f' g'
  change ((relativeFunctorVertexIsoImage p a f g hf hg e).precomp i).postcomp p = _
  rw [functorIso_precomp_postcomp, relativeFunctorVertexIsoImage_postcomp,
    functorIsoEq_precomp (hf.trans hg.symm) i]

/-- 指定された同じ辺のprismを前合成すると、その辺の前合成のprismになる。 -/
lemma functorEdgePrism_precomp {A D X : SSet.{u}} {f g : A ⟶ X}
    (e : Truncated.Edge (X := (truncation 2).obj ((ihom A).obj X))
      (functorVertex f) (functorVertex g)) (i : D ⟶ A) :
    functorEdgePrism (F := i ≫ f) (G := i ≫ g)
      (e.map ((truncation 2).map ((pre i).app X))) =
      (Δ[1] ◁ i) ≫ functorEdgePrism e := by
  unfold functorEdgePrism
  change functorFamilyPrism (SSet.yonedaEquiv.symm (((pre i).app X).app _ e.edge)) = _
  rw [← SSet.yonedaEquiv_symm_comp, functorFamilyPrism_pre]
  rfl

/-- 指定相対同型の底変換の順方向は、同じ第一射影の頂点同型を与える。 -/
lemma relativeFunctorBaseChangeForward_vertexIso {A E B D : SSet.{u}}
    (p : E ⟶ B) (k : D ⟶ B) (a : A ⟶ D) (f g : A ⟶ pullback p k)
    (hf : f ≫ pullback.snd p k = a) (hg : g ≫ pullback.snd p k = a)
    (e : VertexIso (relativeFunctorVertex (pullback.snd p k) a f hf)
      (relativeFunctorVertex (pullback.snd p k) a g hg)) :
    ∃ (hf' : (f ≫ pullback.fst p k) ≫ p = a ≫ k)
      (hg' : (g ≫ pullback.fst p k) ≫ p = a ≫ k),
      Nonempty (VertexIso (relativeFunctorVertex p (a ≫ k) (f ≫ pullback.fst p k) hf')
        (relativeFunctorVertex p (a ≫ k) (g ≫ pullback.fst p k) hg')) := by
  have hf' : (f ≫ pullback.fst p k) ≫ p = a ≫ k := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hf]
  have hg' : (g ≫ pullback.fst p k) ≫ p = a ≫ k := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hg]
  let m := relativeFunctorBaseChangeForward p k a
  have hL : m.app _ (relativeFunctorVertex (pullback.snd p k) a f hf) =
      relativeFunctorVertex p (a ≫ k) (f ≫ pullback.fst p k) hf' :=
    relativeFunctorBaseChangeForward_vertex p k a f hf
  have hR : m.app _ (relativeFunctorVertex (pullback.snd p k) a g hg) =
      relativeFunctorVertex p (a ≫ k) (g ≫ pullback.fst p k) hg' :=
    relativeFunctorBaseChangeForward_vertex p k a g hg
  exact ⟨hf', hg', ⟨(eqToIso (congrArg HomotopyCategory.mk hL)).symm ≪≫ e.map m ≪≫
    eqToIso (congrArg HomotopyCategory.mk hR)⟩⟩

/-- 同じ端点等式による二つの標準移送は、同じ指定同型を与える。 -/
lemma functorIsoOfEq_eq_diagramIsoCongr {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (e : FunctorIso f g) (hf : f = f') (hg : g = g') :
    functorIsoOfEq e hf hg = diagramIsoCongr hf hg e :=
  eq_of_heq ((functorIsoOfEq_heq e hf hg).trans (diagramIsoCongr_heq hf hg e).symm)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

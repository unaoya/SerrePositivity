module

public import SerrePositivity.KST.Spectra.D3FiberPathIsoComparison

/-!
概要：既存の path 補正成分同型が、持ち上げた同じ指定 path の辺の類に一致すると認証。
方針：元の fiber 比較の値を回収し、端点表示だけを輸送して exact 表示と照合する。
規約：既存 componentIso の選択を置き換えない。使われ方：元の切断補正の終点値の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra

/-- 元の path を uncurry して作る同じ lift は、全単体で元の path そのもの。 -/
lemma d3EquivalencePathLift_uncurry {A Y : SSet.{u}} [Quasicategory Y]
    (L : A ⟶ equivalencePath Y)
    (hH : ∀ x : A _⦋0⦌, IsInvertibleEdge (edgeOfSimplex
      ((uncurry (L ≫ equivalencePathι Y)).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1)))) :
    F2.equivalenceHomotopyPathLift (uncurry (L ≫ equivalencePathι Y)) hH = L := by
  have h := (F2.equivalenceHomotopyPathLift_ι
    (uncurry (L ≫ equivalencePathι Y)) hH).trans (curry_uncurry (L ≫ equivalencePathι Y))
  exact (cancel_mono (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj Y)
    IsEquivalencePathVertex).ι).1 h

/-- 既存の Kan path 族から作る同型は、元の同じ path の指定同型に一致する。 -/
lemma d3KanEquivalencePathFunctorIso_value {A Y : SSet.{u}} [Quasicategory Y]
    (L : A ⟶ equivalencePath Y) :
    HEq (F1B.kanEquivalencePath_functorIso L) (equivalencePathFamilyIso L) := by
  unfold F1B.kanEquivalencePath_functorIso
  refine (cast_heq _ _).trans ((cast_heq _ _).trans ?_)
  refine (d3TrivialPathFiberIso_value _
    (prismEndpoint 0 A ≫ uncurry (L ≫ equivalencePathι Y)) _).trans ?_
  apply d3EquivalencePathFamilyIso_of_eq
  apply (cancel_mono (fullSubcomplexOnVertices ((ihom (Δ[1] : SSet.{u})).obj Y)
    IsEquivalencePathVertex).ι).1
  simpa only [fullSubcomplexLift_ι, equivalencePathι] using (curry_uncurry (L ≫ equivalencePathι Y))

/-- 関手同型の同じ順射の値と端点表示は、同型全体の型付き一致を決める。 -/
lemma d3FunctorIso_heq_of_hom_heq {A X : SSet.{u}} {f g f' g' : A ⟶ X}
    (e : FunctorIso f g) (e' : FunctorIso f' g') (hf : f = f') (hg : g = g')
    (hh : HEq e.hom e'.hom) : HEq e e' := by
  subst f' g'
  exact heq_of_eq (Iso.ext (eq_of_heq hh))

section
variable {A E B : SSet.{u}} [Quasicategory E] [Quasicategory B]
  {q : E ⟶ B} {f : A ⟶ E} {g : A ⟶ B} {e : FunctorIso g (f ≫ q)}
  (s : PathCorrectedFunctorSquare q f g e)

/-- 元の既存 componentIso は、同じ指定 path の同型の端点表示に一致する。 -/
lemma d3PathCorrectedComponentIso_value :
    HEq s.componentIso (equivalencePathFamilyIso s.path) := by
  unfold PathCorrectedFunctorSquare.componentIso
  refine (cast_heq _ _).trans ((cast_heq _ _).trans ?_)
  exact d3KanEquivalencePathFunctorIso_value s.path

/-- 同じ exact 表示も、同じ指定 path の同型の同じ順射を保持する。 -/
lemma d3PathCorrectedExactComponentIso_value :
    HEq s.exactComponentIso (equivalencePathFamilyIso s.path) := by
  apply d3FunctorIso_heq_of_hom_heq _ _ s.zero.symm s.one.symm
  change HEq (SSet.Truncated.HomotopyCategory.homMk s.componentEdge.toTruncated)
    (SSet.Truncated.HomotopyCategory.homMk (equivalencePathFamilyEdge s.path).toTruncated)
  exact d3HomMk_heq _ _ (congrArg functorVertex s.zero.symm)
    (congrArg functorVertex s.one.symm) rfl

/-- 元の選択を変更せず、既存 componentIso と同じ path による exact 表示の一致を認証。 -/
lemma d3PathCorrectedComponentIso_eq_exact : s.componentIso = s.exactComponentIso := by
  exact eq_of_heq ((d3PathCorrectedComponentIso_value s).trans
    (d3PathCorrectedExactComponentIso_value s).symm)

/-- 既存 componentIso の標的像も、元の指定自然性同型そのものを回収する。 -/
lemma d3PathCorrectedComponentIso_postcomp :
    s.componentIso.postcomp q =
      eqToIso (congrArg
        (fun v : A ⟶ B ↦ SSet.HomotopyCategory.mk (functorVertex v)) s.comm) ≪≫ e := by
  rw [d3PathCorrectedComponentIso_eq_exact]
  exact s.exactComponentIso_postcomp
end

end SerrePositivity.KST.Spectra

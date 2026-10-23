module
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftFibrationSpanStrictification
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorEssentialExtension
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorEvaluation

/-! # 元の指定 span との相対三角比較をデータとして保持する、底上の実比較 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 指定した元の span の二脚と、その同じ span 上の相対三角比較を保持する。 -/
structure SpanCompatibleComparison {E F Z B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) (r : Z ⟶ B)
    (a : Z ⟶ E) (b : Z ⟶ F) (ha : a ≫ p = r) (hb : b ≫ q = r) where
  hom : E ⟶ F
  over : hom ≫ q = p
  triangle : VertexIso
    (relativeFunctorVertex q r (a ≫ hom) (by rw [Category.assoc, over, ha]))
    (relativeFunctorVertex q r b hb)
  equivalence : IsPrecompositionEquivalence hom

/-- 元の指定 span を保つ比較は、同じ相対前合成の本質的全射性から構成できる。 -/
theorem nonempty_spanCompatibleComparison {E F Z B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration q] (r : Z ⟶ B)
    (a : Z ⟶ E) (b : Z ⟶ F) (ha : a ≫ p = r) (hb : b ≫ q = r)
    (ea : IsPrecompositionEquivalence a) (eb : IsPrecompositionEquivalence b) :
    Nonempty (SpanCompatibleComparison p q r a b ha hb) := by
  have : Quasicategory F := quasicategory_of_innerFibration q
  let a' : Over.mk r ⟶ Over.mk p := Over.homMk a ha
  have he := relativeFunctorOverPre_isQCatEquivalence q a' ea
  obtain ⟨v, ⟨h⟩⟩ := he.choose.isEssentiallySurjective (relativeFunctorVertex q r b hb)
  obtain ⟨f, hf, hv⟩ := exists_relativeFunctorVertex q p v
  rw [← hv] at h
  change VertexIso
    ((relativeFunctorOverPre q a').app (Opposite.op ⦋0⦌) (relativeFunctorVertex q p f hf))
    (relativeFunctorVertex q r b hb) at h
  have ht := relativeFunctorOverPre_vertex q a' f hf
  have hn : VertexIso
      (relativeFunctorVertex q r (a ≫ f) (by rw [Category.assoc, hf, ha]))
      (relativeFunctorVertex q r b hb) :=
    (eqToIso (congrArg HomotopyCategory.mk ht)).symm ≪≫ h
  have h' : FunctorIso (a ≫ f) b := VertexIso.map hn
    (vertexFiberι ((ihom Z).map q) (functorVertex r))
  have hcomp : IsPrecompositionEquivalence (a ≫ f) :=
    (isPrecompositionEquivalence_iff_of_homotopy h'.simplicialHomotopy
      (simplicialHomotopyOfFunctorEdge_vertex_isInvertible
        (FunctorIso.edge h') (FunctorIso.edge_isInvertible h'))).mpr eb
  exact ⟨⟨f, hf, hn, ea.cancel_left hcomp⟩⟩

/-- 選ぶ対象には相対三角比較も含め、元の span との対応を保持する。 -/
def spanCompatibleComparison {E F Z B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration q] (r : Z ⟶ B)
    (a : Z ⟶ E) (b : Z ⟶ F) (ha : a ≫ p = r) (hb : b ≫ q = r)
    (ea : IsPrecompositionEquivalence a) (eb : IsPrecompositionEquivalence b) :
    SpanCompatibleComparison p q r a b ha hb :=
  Classical.choice (nonempty_spanCompatibleComparison p q r a b ha hb ea eb)

/-- 保持した同じ相対三角比較を、元の共通全空間の指定点で評価する。 -/
def SpanCompatibleComparison.pointIso {E F Z B : SSet.{u}}
    {p : E ⟶ B} {q : F ⟶ B} {r : Z ⟶ B}
    {a : Z ⟶ E} {b : Z ⟶ F} {ha : a ≫ p = r} {hb : b ≫ q = r}
    (c : SpanCompatibleComparison p q r a b ha hb) (z : Z _⦋0⦌) :
    VertexIso
      ((relativeFunctorEvaluate q r z).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex q r (a ≫ c.hom) (by rw [Category.assoc, c.over, ha])))
      ((relativeFunctorEvaluate q r z).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex q r b hb)) :=
  VertexIso.map c.triangle (relativeFunctorEvaluate q r z)

end SerrePositivity.KST.Fibration

module

public import SerrePositivity.InfinityCategories.Core.Equivalence
public import SerrePositivity.InfinityCategories.Core.LeftFiberKan
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.SimplicialHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanFilling
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanSequence
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.ContinuousKanWeakEquivalence
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.F1B.Homotopy.WeakWhitehead
public import SerrePositivity.InfinityCategories.F1B.KanComplex.HomotopyClasses
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.ContinuousKanFiniteFactorization
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.ContinuousKanHomotopy
public import SerrePositivity.InfinityCategories.Core.Filtered.FilteredInfinity
public import SerrePositivity.InfinityCategories.F1.Filtered.FilteredLeftFibrationTransport
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.FiniteSubcomplexes

/-!
概要：filtered な底の left fibration の Kan 置換への有限射を一つの fiber で検出する。
方針：元の有限部分複体へ因子分解し、その底の余錐に沿う輸送を Kan 置換へ送る。
規約：任意の filtered ∞ 圏を扱い、通常の小圏による表示を仮定しない。
使われ方：一般 coherent な空間値図式の余極限模型の有限検査。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：全空間の Kan 置換への有限射は、一つの fiber の Kan 置換で表せる。
方針：有限部分複体の因子分解と底の filtered 性による輸送を合成する。
規約：比較は元の指定射との実際のホモトピー。使われ方：coherent 余極限の有限検出。 -/
lemma continuousKanLeftFibration_finite_fiber_detection {K E B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (f : K ⟶ continuousKanReplacement.obj E) :
    ∃ b : B _⦋0⦌, ∃ g : K ⟶ continuousKanReplacement.obj (vertexFiber p b),
      Nonempty (SSet.Homotopy f (g ≫ continuousKanReplacement.map (vertexFiberι p b))) := by
  obtain ⟨A, a, ha⟩ := continuousKanReplacement_finite_factorization f
  obtain ⟨b, g, ⟨H⟩⟩ := leftFibration_finite_fiber_detection p A.val.ι
  obtain ⟨H'⟩ := continuousKanReplacement_map_homotopy H
  refine ⟨b, a ≫ continuousKanReplacement.map g, ?_⟩
  have h := functorHomotopyPrecomp H' a
  simpa only [CategoryTheory.Functor.map_comp, ← Category.assoc, ha] using Nonempty.intro h

attribute [local instance] vertexFiber_kanComplex_of_leftFibration

/-- 概要：有限射は Kan 置換前の実際の fiber への射でも表せる。
方針：fiber は Kan なので単位のホモトピー逆で置換を除く。
規約：全空間への包含の後の単位との比較。使われ方：元の図式の値による有限検出。 -/
lemma continuousKanLeftFibration_finite_fiber_detection_unreplaced {K E B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (f : K ⟶ continuousKanReplacement.obj E) :
    ∃ b : B _⦋0⦌, ∃ g : K ⟶ vertexFiber p b,
      Nonempty (SSet.Homotopy f
        (g ≫ vertexFiberι p b ≫ continuousKanReplacementUnit.app E)) := by
  obtain ⟨b, g, ⟨H⟩⟩ := continuousKanLeftFibration_finite_fiber_detection p f
  have : KanComplex ((𝟭 SSet.{u}).obj (vertexFiber p b)) :=
    vertexFiber_kanComplex_of_leftFibration p b
  obtain ⟨r, _, ⟨Hr⟩⟩ := (continuousKanReplacementUnit_isWeakHomotopyEquivalence
    (vertexFiber p b)).isSimplicialHomotopyEquivalence
  refine ⟨b, g ≫ r, (functorVertex_piZero_eq_iff_homotopy _ _).1 ?_⟩
  have h₁ := (functorVertex_piZero_eq_iff_homotopy _ _).2 ⟨H⟩
  have h₂ := (functorVertex_piZero_eq_iff_homotopy _ _).2
    ⟨functorHomotopyPrecomp
      (functorHomotopyPostcomp Hr (continuousKanReplacement.map (vertexFiberι p b))) g⟩
  simp only [Category.assoc, Category.id_comp,
    ← continuousKanReplacementUnit.naturality (vertexFiberι p b)] at h₂
  simpa only [Category.assoc, CategoryTheory.Functor.id_map] using h₁.trans h₂.symm

end SerrePositivity.InfinityCategories.F2

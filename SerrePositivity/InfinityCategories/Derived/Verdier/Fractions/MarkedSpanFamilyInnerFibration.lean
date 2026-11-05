module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanFamilyFiber

/-!
概要：第一終点固定の分母付き span の第二終点射影は inner fibration。
方針：指定した第二終点族と定値第一終点を境界図式へまとめ、境界制限で持ち上げる。
規約：既存のホーン族と標的の全単体を厳密に保持する。
使われ方：分数 span 族の cocartesian fibration 性の第一条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

lemma intervalBoundaryCurry_source {A X : SSet.{u}} (f g : A ⟶ X) :
    curry (intervalBoundaryDiagram f g) ≫ evaluateFunctorAt
      (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 2), vertex_mem_boundary 0 0⟩ :
        (boundary 1 : SSet.{u}) _⦋0⦌) = f := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro v
  change f.app (Opposite.op ⦋n⦌) (A.map (𝟙 _) v) = _
  rw [CategoryTheory.Functor.map_id_apply]

lemma intervalBoundaryCurry_target {A X : SSet.{u}} (f g : A ⟶ X) :
    curry (intervalBoundaryDiagram f g) ≫ evaluateFunctorAt
      (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 2), vertex_mem_boundary 0 1⟩ :
        (boundary 1 : SSet.{u}) _⦋0⦌) = g := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro v
  change g.app (Opposite.op ⦋n⦌) (A.map (𝟙 _) v) = _
  rw [CategoryTheory.Functor.map_id_apply]

lemma markedSpanFamily_boundary {A X : SSet.{u}} (W : Set (X _⦋1⦌))
    (x : X _⦋0⦌) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamily X W x) :
    (f ≫ vertexFiberι (markedSpanSource X W) x) ≫ markedSpanBoundary X W =
      curry (intervalBoundaryDiagram (SSet.const x) (f ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection X W x)) := by
  rw [markedSpanBoundary, ← curry_natural_left, intervalBoundaryDiagram_naturality,
    Category.assoc, vertexFiberι_comp, SSet.comp_const]
  rfl

instance markedSpanFamilyProjection_innerFibration (X : SSet.{u}) [Quasicategory X]
    (W : Set (X _⦋1⦌)) (x : X _⦋0⦌) : InnerFibration (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection X W x) where
  mem := by
    intro A B i hi
    have := InnerFibration.mem (q := markedSpanBoundary X W) i hi
    constructor
    intro a b sq
    let d := curry (intervalBoundaryDiagram (SSet.const x : B ⟶ X) b)
    have hd : (a ≫ vertexFiberι (markedSpanSource X W) x) ≫ markedSpanBoundary X W = i ≫ d := by
      rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamily_boundary]
      dsimp only [d]
      rw [← curry_natural_left, intervalBoundaryDiagram_naturality, SSet.comp_const, sq.w]
    let t : CommSq (a ≫ vertexFiberι (markedSpanSource X W) x) i (markedSpanBoundary X W) d := ⟨hd⟩
    have hs : t.lift ≫ markedSpanSource X W = SSet.const x := by
      calc
        t.lift ≫ markedSpanSource X W = (t.lift ≫ markedSpanBoundary X W) ≫
            evaluateFunctorAt (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 2),
              vertex_mem_boundary 0 0⟩ : (boundary 1 : SSet.{u}) _⦋0⦌) := by
          rw [Category.assoc, markedSpanBoundary_source]
        _ = d ≫ evaluateFunctorAt (⟨stdSimplex.obj₀Equiv.symm (0 : Fin 2),
              vertex_mem_boundary 0 0⟩ : (boundary 1 : SSet.{u}) _⦋0⦌) :=
          congrArg (fun f : B ⟶ (ihom (boundary 1 : SSet.{u})).obj X =>
            f ≫ evaluateFunctorAt _) t.fac_right
        _ = SSet.const x := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.intervalBoundaryCurry_source _ _
    let G := vertexFiberLift (markedSpanSource X W) x t.lift hs
    refine CommSq.HasLift.mk' { l := G, fac_left := ?_, fac_right := ?_ }
    · apply (cancel_mono (vertexFiberι (markedSpanSource X W) x)).mp
      rw [Category.assoc, vertexFiberLift_ι]
      exact t.fac_left
    · change (G ≫ vertexFiberι (markedSpanSource X W) x) ≫ markedSpanTarget X W = b
      rw [vertexFiberLift_ι]
      calc
        t.lift ≫ markedSpanTarget X W = (t.lift ≫ markedSpanBoundary X W) ≫
            evaluateFunctorAt (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 2),
              vertex_mem_boundary 0 1⟩ : (boundary 1 : SSet.{u}) _⦋0⦌) := by
          rw [Category.assoc, markedSpanBoundary_target]
        _ = d ≫ evaluateFunctorAt (⟨stdSimplex.obj₀Equiv.symm (1 : Fin 2),
              vertex_mem_boundary 0 1⟩ : (boundary 1 : SSet.{u}) _⦋0⦌) :=
          congrArg (fun f : B ⟶ (ihom (boundary 1 : SSet.{u})).obj X =>
            f ≫ evaluateFunctorAt _) t.fac_right
        _ = b := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.intervalBoundaryCurry_target _ _

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.intervalBoundaryCurry_source := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.intervalBoundaryCurry_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.intervalBoundaryCurry_target := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.intervalBoundaryCurry_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection_innerFibration (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.markedSpanFamilyProjection_innerFibration := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamilyProjection_innerFibration

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.markedSpanFamily_boundary := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.markedSpanFamily_boundary

module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ReflectedBousfieldKanColimit
public import SerrePositivity.InfinityCategories.HomotopyLimits.GeneralHomHolimComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictNativeCocones
public import SerrePositivity.InfinityCategories.F1.Coherent.Vertices
public import SerrePositivity.InfinityCategories.Stable.ColimitExistenceTransfer

/-!
概要：一般の Kan 値図式の反転 coend から、元の図式上の実際の coherent な余錐を構成する。
方針：反転 Hom の比較と coherent 錐の切断比較を合成し、恒等射の普遍要素を余錐へ戻す。
規約：頂点は実際の Kan 置換した coend。余極限性そのものはまだ主張しない。
使われ方：HTT 4.2.4.1、γ3c の一般の小図式の余極限を証明する余錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {I : Type u} [SmallCategory I]

local instance bkCoconeOppositeHomKan (X Y : KanObject.{u}ᵒᵖ) :
    KanComplex (SimplicialCategory.sHom X Y) :=
  inferInstanceAs (KanComplex (SimplicialCategory.sHom Y.unop X.unop))

/-- Kan 置換した coend の反転 Hom から、全ての coherent な錐の切断模型への比較。 -/
def bousfieldKanCoherentConeComparison (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj
        (SimplicialCategory.sHom (kanReflectedBousfieldKanColimitObject F) Y).op ⟶
      coherentConeSectionSpace (strictCoherentDiagram F.op)
        (coherentNerveVertex (Opposite.op Y)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (kanReflectedBousfieldKanColimitHomComparison F Y) ≫
    reflectedHomHolimConeComparison F.op (Opposite.op Y)

/-- coend の反転 Hom と coherent な錐の切断模型の実際の比較はホモトピー同値。 -/
lemma bousfieldKanCoherentConeComparison_homotopyEquivalence
    (F : I ⥤ KanObject.{u}) (Y : KanObject.{u}) :
    IsSimplicialHomotopyEquivalence (bousfieldKanCoherentConeComparison F Y) := by
  have : ∀ i, KanComplex
      ((simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (SimplicialCategory.sHom (F.obj i.unop) Y).op)
  have := bousfieldKanHolim_kanComplex
    (simplicialHomDiagram F.op (Opposite.op Y) ⋙ SSet.opFunctor)
  exact (DoldKanComparison.ulift_homotopyEquivalence.{u, u + 1}
    (kanReflectedBousfieldKanColimitHomComparison_homotopyEquivalence F Y)).comp
      (reflectedHomHolimConeComparison_homotopyEquivalence F.op (Opposite.op Y))

/-- 恒等射を比較で送って得られる、coend を頂点に持つ coherent な錐の切断点。 -/
def bousfieldKanCoherentConePoint (F : I ⥤ KanObject.{u}) :
    (coherentConeSectionSpace (strictCoherentDiagram F.op)
      (coherentNerveVertex (Opposite.op (kanReflectedBousfieldKanColimitObject F)))) _⦋0⦌ :=
  (bousfieldKanCoherentConeComparison F (kanReflectedBousfieldKanColimitObject F)).app _
    (ULift.up (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' _ _ (𝟙 _))))

/-- 普遍切断点に対応する反対圏内の実際の coherent な錐。 -/
def bousfieldKanCoherentOppositeCone (F : I ⥤ KanObject.{u}) :
    JoinCone (strictCoherentDiagram F.op) :=
  ((fixedVertexConeSpaceEquiv (strictCoherentDiagram F.op)
    (coherentNerveVertex (Opposite.op (kanReflectedBousfieldKanColimitObject F)))).symm
      (bousfieldKanCoherentConePoint F)).val

/-- 切断点から作った錐の頂点は指定した Kan coend の反対対象。 -/
lemma bousfieldKanCoherentOppositeCone_vertex (F : I ⥤ KanObject.{u}) :
    (bousfieldKanCoherentOppositeCone F).vertex =
      coherentNerveVertex (Opposite.op (kanReflectedBousfieldKanColimitObject F)) := by
  have h := ((fixedVertexConeSpaceEquiv (strictCoherentDiagram F.op)
    (coherentNerveVertex (Opposite.op (kanReflectedBousfieldKanColimitObject F)))).symm
      (bousfieldKanCoherentConePoint F)).property
  rw [JoinCone.vertex_eq]
  change SSet.yonedaEquiv (joinInl Δ[0] _ ≫ (bousfieldKanCoherentOppositeCone F).val) = _
  exact (congrArg SSet.yonedaEquiv h).trans (Equiv.apply_symm_apply _ _)

/-- 反対の coherent な錐を、元の標準図式上の native な余錐へ戻す。 -/
def bousfieldKanCoherentCocone (F : I ⥤ KanObject.{u}) :
    JoinCocone (kanDiagramCoherentNerve F) :=
  coherentCoconeOfDiagramEq (strictCoherentDiagram_eq_kanDiagram F)
    (coherentCoconeOfDiagramEq (strictCoherentCoconeDiagram_eq F)
      (coherentCoconePost ((bousfieldKanCoherentOppositeCone F).reverseCocone.restrict
        (strictCoconeIndexIso.{u, u + 1} I).hom) (coherentOppositeReturnIso KanObject.{u}).hom))

/-- 元の図式上に戻した余錐も実際の Kan 置換した coend を頂点に持つ。 -/
lemma bousfieldKanCoherentCocone_vertex (F : I ⥤ KanObject.{u}) :
    (bousfieldKanCoherentCocone F).vertex =
      spaceInfinityVertex (kanReflectedBousfieldKanColimitObject F) := by
  rw [bousfieldKanCoherentCocone, coherentCoconeOfDiagramEq_vertex,
    coherentCoconeOfDiagramEq_vertex, coherentCoconePost_vertex, JoinCocone.vertex_restrict,
    JoinCone.reverseCocone_vertex, bousfieldKanCoherentOppositeCone_vertex,
    spaceInfinityVertex_eq_coherent]
  exact coherentOppositeReturnIso_hom_vertex _

end
end SerrePositivity.InfinityCategories.HomotopyLimits

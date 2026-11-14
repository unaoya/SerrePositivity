module

public import SerrePositivity.KST.LocalizingInvariants.LaxDAdjunction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialVertexIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.VerdierSequence

/-!
概要：元の lax pullback の第一射影の核は、D 包含の本質像に一致する。
方針：第一成分が零である対象と D 包含の対象が、ともに第二射影に相対的に始対象となる。
規約：核の生成を追加仮定にしない。使われ方：K-8 の実半直交分解と Verdier 列。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.LaxInclusion

variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma fromD_snd_vertex (x : D.obj _⦋0⦌) :
    (laxSnd p q).hom.app (Opposite.op ⦋0⦌) ((fromD p q).app (Opposite.op ⦋0⦌) x) = x := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app (fromD_snd p q)
    (Opposite.op ⦋0⦌)) x
  exact h

lemma fst_kernel (x : (laxCategory p q).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((laxFst p q).hom.app (Opposite.op ⦋0⦌) x) ↔
      x ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.essentialImage (exactFromD p q) := by
  constructor
  · intro hx
    let d := (laxSnd p q).hom.app (Opposite.op ⦋0⦌) x
    have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (laxSnd p q).hom x :=
      lax_snd_initialBoundary p.hom q.hom x hx.1
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := p.hom) _ hx).1
    let e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((laxSnd p q).hom.app (Opposite.op ⦋0⦌)
        ((fromD p q).app (Opposite.op ⦋0⦌) d))
        ((laxSnd p q).hom.app (Opposite.op ⦋0⦌) x) :=
      eqToIso (congrArg SSet.HomotopyCategory.mk (fromD_snd_vertex p q d))
    exact ⟨d, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.relativeInitialVertexIso (laxSnd p q).hom _ _
      (fromD_initialBoundary p q d) hi e⟩⟩
  · rintro ⟨d, ⟨e⟩⟩
    have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((laxFst p q).hom.app (Opposite.op ⦋0⦌)
        ((fromD p q).app (Opposite.op ⦋0⦌) d)) := by
      change _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackFst p.hom q.hom).app (Opposite.op ⦋0⦌) _)
      rw [fromD_fst_vertex]
      exact (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex C.obj).isZero
    exact hz.of_vertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (laxFst p q).hom)

end SerrePositivity.KST.LocalizingInvariants.LaxInclusion

module

public import SerrePositivity.KST.LocalizingInvariants.StableCofiberWide
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableClosureFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion

/-!
概要：完全充満忠実関手の元の本質像を保つ cofiber 分母の wide 部分圏を構成する。
方針：h 圏の三角的本質像で安定閉包を照合し、実全辺条件の部分複体を使う。
規約：安定閉包は元の本質像に等しく、retract 閉包への拡大を行わない。
使われ方：Sp-7 の冪等完備化の入力と K-cof への供給。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D : SSet.{u}} [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
  (f : C ⟶ D) [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f]

/-- 概要：元の完全関手の頂点の本質像。
方針：h 圏の三角的本質像で安定閉包を照合し、実全辺条件の部分複体を使う。
規約：安定閉包は元の本質像に等しく、retract 閉包への拡大を行わない。
使われ方：Sp-7 の冪等完備化の入力と K-cof への供給。 -/
def completionEssentialImage : Set (D _⦋0⦌) :=
  {y | ∃ x : C _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.app (Opposite.op ⦋0⦌) x) y)}

/-- 概要：完全充満忠実な包含の本質像は、元の安定閉包と等しい。
方針：h 圏の三角的本質像で安定閉包を照合し、実全辺条件の部分複体を使う。
規約：安定閉包は元の本質像に等しく、retract 閉包への拡大を行わない。
使われ方：Sp-7 の冪等完備化の入力と K-cof への供給。 -/
lemma stableClosure_completionEssentialImage (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful f) :
    {y | _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (completionEssentialImage f) y} = completionEssentialImage f := by
  let H := (hoFunctor.map f).toFunctor
  let : H.Full := hf.toHoFullyFaithful.full
  let : H.Faithful := hf.toHoFullyFaithful.faithful
  let Q := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (Set.univ : Set (C _⦋0⦌))).map H
  have hle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure (completionEssentialImage f) ≤ Q := by
    apply (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHoClosure_le_iff _ Q).2
    rintro y ⟨x, ⟨e⟩⟩
    exact ⟨HomotopyCategory.mk x, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem (Set.mem_univ x), ⟨e⟩⟩
  ext y
  constructor
  · intro hy
    obtain ⟨x, _, ⟨e⟩⟩ := hle (HomotopyCategory.mk y) hy
    obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective x
    exact ⟨x, ⟨e⟩⟩
  · exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure.of_mem

/-- 概要：全単体の全辺が、元の本質像に cofiber を持つことを要求する部分複体。
方針：h 圏の三角的本質像で安定閉包を照合し、実全辺条件の部分複体を使う。
規約：安定閉包は元の本質像に等しく、retract 閉包への拡大を行わない。
使われ方：Sp-7 の冪等完備化の入力と K-cof への供給。 -/
def completionCofiberWide : D.Subcomplex :=
  edgewiseSubcomplex (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f))

omit [Quasicategory C] [Quasicategory D] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable D]
  [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f] in
@[simp] lemma completionCofiberWide_mem (n : ℕ) (s : D _⦋n⦌) :
    s ∈ (completionCofiberWide f).obj (Opposite.op ⦋n⦌) ↔
      ∀ θ : ⦋1⦌ ⟶ ⦋n⦌, D.map θ.op s ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (completionEssentialImage f) :=
  Iff.rfl

/-- 概要：同じ元の本質像に対する wide 部分複体は quasicategory。
方針：h 圏の三角的本質像で安定閉包を照合し、実全辺条件の部分複体を使う。
規約：安定閉包は元の本質像に等しく、retract 閉包への拡大を行わない。
使われ方：Sp-7 の冪等完備化の入力と K-cof への供給。 -/
lemma completionCofiberWide_quasicategory (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f) :
    Quasicategory (completionCofiberWide f : SSet.{u}) := by
  have he : completionCofiberWide f = stableCofiberWide (completionEssentialImage f) := by
    unfold completionCofiberWide stableCofiberWide
    rw [stableClosure_completionEssentialImage f h.2.1]
  rw [he]
  infer_instance

end SerrePositivity.KST.LocalizingInvariants

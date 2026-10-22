module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorVertices
public import SerrePositivity.InfinityCategories.F1.LeftFibrationInfinityEquivalence

/-!
概要：同じ底上の同値 span を、元の右脚との相対比較を保つ left fibration 間の同値射へ移す。
方針：相対前合成の本質的全射性で射を戻し、元の脚の同値性と二対三則で判定する。
規約：共通始域には inner fibration 性だけを要求する。新たな left fibration 仮定を置かない。
使われ方：under 切断の復元 span を、共同 straightening の分類比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の span の右脚を相対同型で回収する、底上の left fibration 間の同値射が存在する。 -/
lemma exists_leftFibrationComparison_of_span {X Y Z S : SSet.{u}} [Quasicategory S]
    (p : X ⟶ S) (q : Y ⟶ S) [LeftFibration p] [LeftFibration q]
    (t : Z ⟶ S) [InnerFibration t] (a : Z ⟶ X) (b : Z ⟶ Y)
    (ha : a ≫ p = t) (hb : b ≫ q = t)
    (ea : IsPrecompositionEquivalence a) (eb : IsPrecompositionEquivalence b) :
    ∃ (f : X ⟶ Y) (hf : f ≫ q = p), IsPrecompositionEquivalence f ∧
      Nonempty (VertexIso
        (relativeFunctorVertex q t (a ≫ f) (by rw [Category.assoc, hf, ha]))
        (relativeFunctorVertex q t b hb)) := by
  have : Quasicategory X := quasicategory_of_innerFibration p
  have : Quasicategory Y := quasicategory_of_innerFibration q
  have : Quasicategory Z := quasicategory_of_innerFibration t
  let a' : Over.mk t ⟶ Over.mk p := Over.homMk a ha
  have he := relativeFunctorOverPre_isQCatEquivalence q a' ea
  obtain ⟨v, ⟨hv⟩⟩ := he.choose.isEssentiallySurjective (relativeFunctorVertex q t b hb)
  obtain ⟨f, hf, hfv⟩ := exists_relativeFunctorVertex q p v
  change VertexIso ((relativeFunctorOverPre q a').app _ v) (relativeFunctorVertex q t b hb) at hv
  rw [← hfv] at hv
  have hpre := relativeFunctorOverPre_vertex q a' f hf
  have hrel : VertexIso
      (relativeFunctorVertex q t (a ≫ f) (by rw [Category.assoc, hf, ha]))
      (relativeFunctorVertex q t b hb) :=
    (eqToIso (congrArg HomotopyCategory.mk hpre)).symm ≪≫ hv
  have hplain := hrel.map (vertexFiberι ((ihom Z).map q) (functorVertex t))
  change FunctorIso (a ≫ f) b at hplain
  have hef : IsPrecompositionEquivalence f := ea.cancel_left
    ((eb.isQCatEquivalence.ofFunctorIso hplain.symm).isPrecompositionEquivalence)
  exact ⟨f, hf, hef, ⟨hrel⟩⟩

/-- 同じ底上の span は、元の二つの left fibration の分類頂点の同型を与える。 -/
def leftFibrationVertexIsoOfSpan {X Y Z S : SSet.{u}} [Quasicategory S]
    (p : X ⟶ S) (q : Y ⟶ S) [LeftFibration p] [LeftFibration q]
    (t : Z ⟶ S) [InnerFibration t] (a : Z ⟶ X) (b : Z ⟶ Y)
    (ha : a ≫ p = t) (hb : b ≫ q = t)
    (ea : IsPrecompositionEquivalence a) (eb : IsPrecompositionEquivalence b) :
    VertexIso (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q) := by
  let h := exists_leftFibrationComparison_of_span p q t a b ha hb ea eb
  exact leftFibrationInfinityVertexIsoOfPrecompositionEquivalence p q h.choose
    h.choose_spec.choose h.choose_spec.choose_spec.1

end SerrePositivity.InfinityCategories.F2.Ind

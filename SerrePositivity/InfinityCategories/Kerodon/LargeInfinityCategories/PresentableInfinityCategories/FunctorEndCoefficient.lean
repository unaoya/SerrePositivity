module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointwiseCompactHom
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.UniverseSSetMaps

/-!
概要：固定した関手 F から、可変関手 G に対する twisted arrow end の係数を構成する。
方針：始点では F、終点では普遍的な G を評価し、元の共同 Hom を合成して curry する。
規約：全ての G に自然な一つの図式とし、各値の写像空間だけで代用しない。
使われ方：P-12 の Fun の全 Hom の極限表示の係数図式。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：end 係数の両端を元の圏の二変数へ送る普遍的な底写像。
方針：始点の F の像と、終点での普遍的な関手の評価を束ねる。
規約：始点の反変性を opFunctor.map F で保持する。
使われ方：元の共同 Hom の pullback の底写像。 -/
def functorEndHomBase {A C : SSet.{u}} (F : A ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow A ⊗ (ihom A).obj C ⟶ C.op ⊗ C :=
  lift (fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft A ≫ SSet.opFunctor.map F)
    (lift (fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight A) (snd _ _) ≫ (ihom.ev A).app C)

/-- 概要：普遍的な end 係数の一辺での制限は元の二つの評価。
方針：直積の射影則と頂点の定値射の合成則を使う。
規約：G の全パラメーターを保持する。使われ方：end の評価脚の同定。 -/
lemma functorEndHomBase_at_vertex {A C : SSet.{u}} (F : A ⟶ C)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow A) _⦋0⦌) :
    lift (SSet.const t) (𝟙 ((ihom A).obj C)) ≫ functorEndHomBase F =
      lift (SSet.const ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft A ≫ SSet.opFunctor.map F).app _ t))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight A).app _ t)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro G
  apply Prod.ext
  · exact congrArg (fun f ↦ f.app n G)
      (SSet.const_comp t (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft A ≫ SSet.opFunctor.map F))
  · have h := congrArg (fun f ↦ f.app n G) (SSet.const_comp t (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight A))
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight A).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant t n.unop.len) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight A).app _ t) n.unop.len at h
    change G.app n (𝟙 n) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight A).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant t n.unop.len)) =
      G.app n (𝟙 n) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight A).app _ t) n.unop.len)
    rw [h]

/-- 概要：全関手 G に自然な twisted arrow end の空間値係数図式。
方針：両端の底写像を共同 Hom へ合成し、twisted arrow 変数を curry する。
規約：図式の宇宙持ち上げを明示する。使われ方：全 Hom の極限錐族の底図式。 -/
def functorEndCoefficient {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C) :
    (SSet.uliftFunctor.{u + 1, u}).obj ((ihom A).obj C) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow A))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  curry ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow A) ((ihom A).obj C)).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map (functorEndHomBase F) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso C.op C).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C)

/-- 概要：end 係数の評価脚は始点固定の共同 Hom と終点での評価の合成。
方針：curry の頂点評価を両端の底写像の計算へ戻す。
規約：関手 G に自然な射の等式。使われ方：各点の compact 性による脚の保存。 -/
lemma functorEndCoefficient_evaluation {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow A) _⦋0⦌) :
    functorEndCoefficient F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up t) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight A).app _ t)) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant (SSet.opObjEquiv
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft A ≫ SSet.opFunctor.map F).app _ t)) := by
  rw [functorEndCoefficient, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant
  simp only [Equiv.symm_apply_apply]
  have hb : lift (SSet.const (ULift.up t))
        (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj ((ihom A).obj C))) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow A) ((ihom A).obj C)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (functorEndHomBase F) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso C.op C).hom =
      (SSet.uliftFunctor.{u + 1, u}).map
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseRight A).app _ t)) ≫
      lift (SSet.const (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft A ≫ SSet.opFunctor.map F).app _ t)))
        (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj C)) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨G⟩
    have h := congrArg (fun f ↦ f.app n G) (functorEndHomBase_at_vertex F t)
    exact congrArg (fun p ↦ (ULift.up p.1, ULift.up p.2)) h
  simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.homInfinityJointEvaluation C) hb

/-- 概要：各点で compact な関手の end 係数の全評価脚は κ-filtered 余極限を保つ。
方針：評価脚の厳密な同定を、評価後の共同 Hom の保存へ適用する。
規約：元の κ を変更しない。使われ方：全 Hom の極限錐族の各脚の保存条件。 -/
lemma functorEndCoefficient_evaluation_preservesKappaFilteredColimits
    {κ : Cardinal.{u}} {A C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (F : A ⟶ C)
    (hF : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (F.app _ a))
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedArrow A) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} κ
      (functorEndCoefficient F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up t)) := by
  rw [functorEndCoefficient_evaluation]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointwiseCompactHom.preservesKappaFilteredColimits_jointHom_evaluation hC
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, SSet.opFunctor_map,
    Equiv.apply_symm_apply] using hF (SSet.opObjEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseLeft A).app _ t))

/-- 概要：各点で compact な関手の全 end 係数は点ごとに κ-filtered 余極限を保つ。
方針：全ての評価脚の保存を関手圏の点ごとの余極限判定でまとめる。
規約：twisted arrow の小ささはこの段階では不要。
使われ方：end の極限関手と合成する前の全図式の保存。 -/
lemma functorEndCoefficient_preservesKappaFilteredColimits
    {κ : Cardinal.{u}} {A C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C) (F : A ⟶ C)
    (hF : ∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (F.app _ a)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} κ (functorEndCoefficient F) := by
  intro I hI hFiltered D c hc
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise
  rintro ⟨t⟩
  have h := functorEndCoefficient_evaluation_preservesKappaFilteredColimits hC F hF t
    I D c hc
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
  change ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c).val ≫ functorEndCoefficient F) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up t) =
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift c).val ≫ (functorEndCoefficient F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up t))
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

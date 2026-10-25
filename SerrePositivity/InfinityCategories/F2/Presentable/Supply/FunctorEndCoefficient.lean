module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.PointwiseCompactHom
public import SerrePositivity.InfinityCategories.F1.Transport.PointFunctorEvaluation
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps

/-!
概要：固定した関手 F から、可変関手 G に対する twisted arrow end の係数を構成する。
方針：始点では F、終点では普遍的な G を評価し、元の共同 Hom を合成して curry する。
規約：全ての G に自然な一つの図式とし、各値の写像空間だけで代用しない。
使われ方：P-12 の Fun の全 Hom の極限表示の係数図式。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：end 係数の両端を元の圏の二変数へ送る普遍的な底写像。
方針：始点の F の像と、終点での普遍的な関手の評価を束ねる。
規約：始点の反変性を opFunctor.map F で保持する。
使われ方：元の共同 Hom の pullback の底写像。 -/
def functorEndHomBase {A C : SSet.{u}} (F : A ⟶ C) :
    TwistedArrow A ⊗ (ihom A).obj C ⟶ C.op ⊗ C :=
  lift (fst _ _ ≫ edgewiseLeft A ≫ SSet.opFunctor.map F)
    (lift (fst _ _ ≫ edgewiseRight A) (snd _ _) ≫ (ihom.ev A).app C)

/-- 概要：普遍的な end 係数の一辺での制限は元の二つの評価。
方針：直積の射影則と頂点の定値射の合成則を使う。
規約：G の全パラメーターを保持する。使われ方：end の評価脚の同定。 -/
lemma functorEndHomBase_at_vertex {A C : SSet.{u}} (F : A ⟶ C)
    (t : (TwistedArrow A) _⦋0⦌) :
    lift (SSet.const t) (𝟙 ((ihom A).obj C)) ≫ functorEndHomBase F =
      lift (SSet.const ((edgewiseLeft A ≫ SSet.opFunctor.map F).app _ t))
        (evaluateFunctorAt ((edgewiseRight A).app _ t)) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro G
  apply Prod.ext
  · exact congrArg (fun f ↦ f.app n G)
      (SSet.const_comp t (edgewiseLeft A ≫ SSet.opFunctor.map F))
  · have h := congrArg (fun f ↦ f.app n G) (SSet.const_comp t (edgewiseRight A))
    change (edgewiseRight A).app n (PinchedHom.constant t n.unop.len) =
      PinchedHom.constant ((edgewiseRight A).app _ t) n.unop.len at h
    change G.app n (𝟙 n) ((edgewiseRight A).app n (PinchedHom.constant t n.unop.len)) =
      G.app n (𝟙 n) (PinchedHom.constant ((edgewiseRight A).app _ t) n.unop.len)
    rw [h]

/-- 概要：全関手 G に自然な twisted arrow end の空間値係数図式。
方針：両端の底写像を共同 Hom へ合成し、twisted arrow 変数を curry する。
規約：図式の宇宙持ち上げを明示する。使われ方：全 Hom の極限錐族の底図式。 -/
def functorEndCoefficient {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C) :
    (SSet.uliftFunctor.{u + 1, u}).obj ((ihom A).obj C) ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (TwistedArrow A))).obj SpaceInfinity.{u} :=
  curry ((HomotopyLimits.uliftTensorIso (TwistedArrow A) ((ihom A).obj C)).inv ≫
    (SSet.uliftFunctor.{u + 1, u}).map (functorEndHomBase F) ≫
      (HomotopyLimits.uliftTensorIso C.op C).hom ≫ homInfinityJointEvaluation C)

/-- 概要：end 係数の評価脚は始点固定の共同 Hom と終点での評価の合成。
方針：curry の頂点評価を両端の底写像の計算へ戻す。
規約：関手 G に自然な射の等式。使われ方：各点の compact 性による脚の保存。 -/
lemma functorEndCoefficient_evaluation {A C : SSet.{u}} [Quasicategory C] (F : A ⟶ C)
    (t : (TwistedArrow A) _⦋0⦌) :
    functorEndCoefficient F ≫ evaluateFunctorAt (ULift.up t) =
      (SSet.uliftFunctor.{u + 1, u}).map
        (evaluateFunctorAt (Y := C) ((edgewiseRight A).app _ t)) ≫
      homInfinityCovariant (SSet.opObjEquiv
        ((edgewiseLeft A ≫ SSet.opFunctor.map F).app _ t)) := by
  rw [functorEndCoefficient, curry_evaluateFunctorAt_vertex]
  unfold homInfinityCovariant
  simp only [Equiv.symm_apply_apply]
  have hb : lift (SSet.const (ULift.up t))
        (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj ((ihom A).obj C))) ≫
      (HomotopyLimits.uliftTensorIso (TwistedArrow A) ((ihom A).obj C)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (functorEndHomBase F) ≫
      (HomotopyLimits.uliftTensorIso C.op C).hom =
      (SSet.uliftFunctor.{u + 1, u}).map
        (evaluateFunctorAt (Y := C) ((edgewiseRight A).app _ t)) ≫
      lift (SSet.const (ULift.up ((edgewiseLeft A ≫ SSet.opFunctor.map F).app _ t)))
        (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj C)) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨G⟩
    have h := congrArg (fun f ↦ f.app n G) (functorEndHomBase_at_vertex F t)
    exact congrArg (fun p ↦ (ULift.up p.1, ULift.up p.2)) h
  simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ homInfinityJointEvaluation C) hb

/-- 概要：各点で compact な関手の end 係数の全評価脚は κ-filtered 余極限を保つ。
方針：評価脚の厳密な同定を、評価後の共同 Hom の保存へ適用する。
規約：元の κ を変更しない。使われ方：全 Hom の極限錐族の各脚の保存条件。 -/
lemma functorEndCoefficient_evaluation_preservesKappaFilteredColimits
    {κ : Cardinal.{u}} {A C : SSet.{u + 1}} [Quasicategory C]
    (hC : HasSmallColimits C) (F : A ⟶ C)
    (hF : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} κ (F.app _ a))
    (t : (TwistedArrow A) _⦋0⦌) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} κ
      (functorEndCoefficient F ≫ evaluateFunctorAt (ULift.up t)) := by
  rw [functorEndCoefficient_evaluation]
  apply preservesKappaFilteredColimits_jointHom_evaluation hC
  simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply, SSet.opFunctor_map,
    Equiv.apply_symm_apply] using hF (SSet.opObjEquiv ((edgewiseLeft A).app _ t))

/-- 概要：各点で compact な関手の全 end 係数は点ごとに κ-filtered 余極限を保つ。
方針：全ての評価脚の保存を関手圏の点ごとの余極限判定でまとめる。
規約：twisted arrow の小ささはこの段階では不要。
使われ方：end の極限関手と合成する前の全図式の保存。 -/
lemma functorEndCoefficient_preservesKappaFilteredColimits
    {κ : Cardinal.{u}} {A C : SSet.{u + 1}} [Quasicategory C]
    (hC : HasSmallColimits C) (F : A ⟶ C)
    (hF : ∀ a : A _⦋0⦌, Compact.IsKappaCompact.{u, u + 1} κ (F.app _ a)) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} κ (functorEndCoefficient F) := by
  intro I hI hFiltered D c hc
  apply isColimitCone_of_pointwise
  rintro ⟨t⟩
  have h := functorEndCoefficient_evaluation_preservesKappaFilteredColimits hC F hF t
    I D c hc
  apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
  change ((JoinCocone.ulift c).val ≫ functorEndCoefficient F) ≫
      evaluateFunctorAt (ULift.up t) =
    (JoinCocone.ulift c).val ≫ (functorEndCoefficient F ≫ evaluateFunctorAt (ULift.up t))
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.F2.Presentable

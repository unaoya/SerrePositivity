module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.RelativeFunctorPullbackLimit
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.RelativeFunctorPostFibration
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.StrictHomotopyLimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationMappingSpaces
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorPostLaws

/-!
概要：同じ底上の left fibrations の一脚 left fibration の引き戻しを豊穣極限として扱う。
方針：相対関手空間の引き戻し普遍性と後合成の Kan fibration 性を使う。
規約：全空間と底を同じ宇宙とし、全豊穣 Hom を保持する。
使われ方：引き戻し内の全共変 Hom の極限錐の構成。

対応節は Kerodon 4.2（Tag 014H）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open HomotopicalAlgebra SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

/-- 概要：left fibrations の豊穣 Hom の後合成は元の相対関手の後合成。
方針：全単体の相対合成と、底上の射の豊穣零単体を照合する。
規約：射 f をホモトピー類に置き換えない。
使われ方：全豊穣 Hom 錐を相対関手の指定錐と同定する。 -/
lemma leftFibration_sHom_post {X : SSet.{u}} (a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject X)
    (f : b ⟶ c) :
    ((SimplicialCategory.sHomFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject X)).obj (Opposite.op a)).map f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost b.val.hom c.val.hom f.left f.w a.val.hom := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext ((ihom a.val.left).map c.val.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.val.hom)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost_ι]
  change ((ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.val.hom a.val.hom)).inv ≫
    (_ ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv b.val c.val f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition a.val b.val c.val) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom a.val.left).map c.val.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.val.hom) = _
  rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorComposition_ι]
  have ht := tensorHom_comp_tensorHom
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorSpace b.val.hom a.val.hom)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv b.val c.val f)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom a.val.left).map b.val.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a.val.hom))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((ihom b.val.left).map c.val.hom) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b.val.hom))
  rw [Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv_ι] at ht
  simp only [id_tensorHom] at ht
  rw [← Category.assoc (_ ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorHomEquiv b.val c.val f), ht]
  rw [tensorHom_def, Category.assoc, whiskerLeft_curry'_comp,
    rightUnitor_naturality_assoc, Iso.inv_hom_id_assoc]

/-- 概要：豊穣 Hom の左作用は相対関手の後合成。
方針：全豊穣 Hom 関手の計算を左作用の表記へ移す。
規約：元の全高次パラメーターを保持する。
使われ方：strict な全錐の成分の簡約。 -/
lemma leftFibration_eHomWhiskerLeft {X : SSet.{u}} (a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject X)
    (f : b ⟶ c) : eHomWhiskerLeft SSet.{u} a f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost b.val.hom c.val.hom f.left f.w a.val.hom :=
  leftFibration_sHom_post a b c f

variable {E D B X : SSet.{u}}
  (p : E ⟶ B) (q : D ⟶ B) (e : E ⟶ X) (d : D ⟶ X) (b : B ⟶ X)
  (hp : p ≫ b = e) (hq : q ≫ b = d)

include hp hq

/-- 概要：引き戻しの射影は元の底への left fibration。
方針：一脚の底変換と第二成分の射影を合成する。
規約：第一射影で書いた元の底への射を保持する。
使われ方：引き戻しを left fibration の対象にする。 -/
lemma relativePullbackProjection_leftFibration [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration d] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.fst p q ≫ e) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativePullback_snd_over p q e d b hp hq]
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration (pullback.snd p q) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.pullback_snd p q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem (p := p))⟩
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrations.comp_mem _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem⟩

/-- 概要：元の底上の三つの left fibrations と二射からなる全 cospan。
方針：元の底上の射を束縛した対象間の射として扱う。
規約：小さい cospan の全射を保持する。
使われ方：分類関手に送る前の全極限図式。 -/
def leftFibrationPullbackDiagram [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration e] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration d] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration b] :
    AsSmall.{u} WalkingCospan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject X :=
  AsSmall.down ⋙ cospan
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf e ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf b from Over.homMk p hp)
    (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf d ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf b from Over.homMk q hq)

/-- 概要：元の引き戻しを頂点とする left fibrations の全錐。
方針：元の二射影を底上の射として束縛する。
規約：頂点を新しい同値模型に取り替えない。
使われ方：coherent nerve の全極限錐への移送。 -/
def leftFibrationPullbackOrdinaryCone
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration e] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration d] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration b] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    Cone (leftFibrationPullbackDiagram p q e d b hp hq) := by
  have := relativePullbackProjection_leftFibration p q e d b hp hq
  let c : PullbackCone
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf e ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf b from Over.homMk p hp)
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf d ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf b from Over.homMk q hq) :=
    PullbackCone.mk
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf (pullback.fst p q ≫ e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf e from
        Over.homMk (pullback.fst p q) rfl)
      (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf (pullback.fst p q ≫ e) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf d from
        Over.homMk (pullback.snd p q) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativePullback_snd_over p q e d b hp hq))
      (by apply Over.OverMorphism.ext; exact pullback.condition)
  exact c.whisker AsSmall.down

/-- 概要：元の引き戻し錐は全豊穣 Hom の極限錐。
方針：豊穣後合成を相対関手後合成と同定し、全パラメーターの普遍性を使う。
規約：各点の写像集合の判定で代用しない。
使われ方：left fibrations の coherent nerve の引き戻し判定。 -/
def leftFibrationPullbackOrdinaryCone_hom_isLimit
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration e] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration d] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration b] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject X) :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (leftFibrationPullbackOrdinaryCone p q e d b hp hq) x) := by
  let r := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorPullbackCone p q e d b hp hq x.val.hom).whisker AsSmall.down
  have hr : IsLimit r := IsLimit.whiskerEquivalence
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorPullbackCone_isLimit p q e d b hp hq x.val.hom)
    (AsSmall.equiv : WalkingCospan ≌ AsSmall.{u} WalkingCospan).symm
  let s := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone (leftFibrationPullbackOrdinaryCone p q e d b hp hq) x
  let i : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (leftFibrationPullbackDiagram p q e d b hp hq) x ≅
      AsSmall.down ⋙ cospan (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost e b p hp x.val.hom)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.relativeFunctorPost d b q hq x.val.hom) :=
    NatIso.ofComponents (fun j ↦ by
      rcases j with ⟨j⟩
      cases j with
      | none => exact Iso.refl _
      | some j => cases j <;> exact Iso.refl _) (by
      intro j k f
      rcases j with ⟨j⟩
      rcases k with ⟨k⟩
      rcases f with ⟨f⟩
      change WidePullbackShape.Hom j k at f
      cases f with
      | id j =>
        cases j with
        | none =>
          simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram, leftFibrationPullbackDiagram,
            AsSmall.down, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf]
          rfl
        | some j => cases j <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram, leftFibrationPullbackDiagram,
            AsSmall.down, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf] <;> rfl
      | term j => cases j <;> simp [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram, leftFibrationPullbackDiagram,
            leftFibration_eHomWhiskerLeft, AsSmall.down, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf])
  apply (IsLimit.equivOfNatIsoOfIso i s r ?_).symm hr
  refine Cone.ext (c := (Cone.postcompose i.hom).obj s) (c' := r) (Iso.refl _) ?_
  intro j
  rcases j with ⟨j⟩
  cases j with
  | none =>
    simp [s, r, i, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone, leftFibrationPullbackOrdinaryCone,
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorPullbackCone, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.relativeFunctorPost_comp,
      leftFibration_eHomWhiskerLeft, AsSmall.down, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf,
        leftFibrationPullbackDiagram]
  | some j =>
    cases j <;>
      simp [s, r, i, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomCone, leftFibrationPullbackOrdinaryCone,
        _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorPullbackCone,
        leftFibration_eHomWhiskerLeft, AsSmall.down, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf,
        leftFibrationPullbackDiagram]

/-- 概要：元の全空間の引き戻しは left fibrations の ∞ 圏でも引き戻し。
方針：全豊穣 Hom の極限性と一脚の Kan fibration 性から native な極限錐へ移す。
規約：底 X に quasicategory 性を要求しない。
使われ方：straightening による全空間値関手の引き戻しの構成。 -/
lemma leftFibrationPullbackCone_isLimit
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration e] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration d] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration b] [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone
      (leftFibrationPullbackOrdinaryCone p q e d b hp hq)) := by
  have (x : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject X) : Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram (leftFibrationPullbackDiagram p q e d b hp hq) x).map
        (AsSmall.up.map WalkingCospan.Hom.inl)) := by
    change Fibration
      (((SimplicialCategory.sHomFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject X)).obj (Opposite.op x)).map
        (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf e ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf b from Over.homMk p hp))
    rw [leftFibration_sHom_post]
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFunctorPost_fibration e b p hp x.val.hom
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_cospan_homLimit _
    (leftFibrationPullbackOrdinaryCone_hom_isLimit p q e d b hp hq)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations

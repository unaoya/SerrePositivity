module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.FunctorEndCoefficient
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.EdgewiseOppositeKanEnriched
public import SerrePositivity.InfinityCategories.F1.TwistedArrow.HomSpace
public import SerrePositivity.InfinityCategories.HomotopyLimits.SimplicialSections

/-!
概要：関手圏の twisted Hom から、end 係数の left fibration の切断空間への比較を構成する。
方針：共通の edgewise 重みで単体と自然変換を評価し、両端固定条件で引き戻す。
規約：この葉では比較射を構成し、その同値性は別に証明する。
使われ方：P-12 の全 Hom の end 極限表示の実際の比較射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：二つの関手の始点と終点を Hom の両変数へ送る底写像。
方針：始点に F、終点に G を作用させる。
規約：twisted arrow の向きを保持する。使われ方：end 係数の left fibration の引き戻し。 -/
def functorEndPairBase {A C : SSet.{u}} (F G : A ⟶ C) :
    TwistedArrow A ⟶ C.op ⊗ C :=
  lift (edgewiseLeft A ≫ SSet.opFunctor.map F) (edgewiseRight A ≫ G)

/-- 概要：end の普遍的な底写像を関手 G に制限すると元の両端写像になる。
方針：普遍評価の G の頂点での値を計算する。
規約：射の厳密な等式。使われ方：end 係数の各図式と分類全空間の同定。 -/
lemma functorEndHomBase_at_functor {A C : SSet.{u}} (F G : A ⟶ C) :
    lift (𝟙 (TwistedArrow A)) (SSet.const (functorVertex G)) ≫ functorEndHomBase F =
      functorEndPairBase F G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro a
  apply Prod.ext
  · rfl
  · rfl

/-- 概要：end 係数の G での図式は元の twisted arrow 射影の底変換の分類図式。
方針：curry の頂点則と両端写像の頂点制限を使う。
規約：図式の頂点の厳密な等式。使われ方：切断空間による極限表示との接続。 -/
lemma functorEndCoefficient_vertex {A C : SSet.{u}} [Quasicategory C] (F G : A ⟶ C) :
    (functorEndCoefficient F).app (Opposite.op ⦋0⦌) (ULift.up (functorVertex G)) =
      functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (functorEndPairBase F G) ≫
        twistedArrowHomInfinity C) := by
  have h := (functorVertex_uncurry_at_vertex (functorEndCoefficient F)
    (ULift.up (functorVertex G))).symm
  rw [functorEndCoefficient, uncurry_curry] at h
  have hb : lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (TwistedArrow A)))
        (SSet.const (ULift.up (functorVertex G))) ≫
      (HomotopyLimits.uliftTensorIso (TwistedArrow A) ((ihom A).obj C)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (functorEndHomBase F) =
      (SSet.uliftFunctor.{u + 1, u}).map (functorEndPairBase F G) := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨a⟩
    exact congrArg ULift.up (congrArg (fun f ↦ f.app n a) (functorEndHomBase_at_functor F G))
  have hh : lift (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj (TwistedArrow A)))
        (SSet.const (ULift.up (functorVertex G))) ≫
      ((HomotopyLimits.uliftTensorIso (TwistedArrow A) ((ihom A).obj C)).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (functorEndHomBase F) ≫
        (HomotopyLimits.uliftTensorIso C.op C).hom ≫ homInfinityJointEvaluation C) =
      (SSet.uliftFunctor.{u + 1, u}).map (functorEndPairBase F G) ≫
        twistedArrowHomInfinity C := by
    simp only [homInfinityJointEvaluation, Iso.hom_inv_id_assoc]
    simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ twistedArrowHomInfinity C) hb
  rw [hh] at h
  exact h

/-- 概要：両端固定の関手圏の twisted Hom の普遍的な評価。
方針：twisted Hom の包含を edgewise な内部 Hom 評価へ合成する。
規約：twisted arrow の単体を全て扱う。使われ方：end の全切断への比較の入力。 -/
def twistedFunctorHomEvaluation {A C : SSet.{u}} (F G : A ⟶ C) :
    TwistedArrow A ⊗ twistedArrowHomSpace (functorVertex F) (functorVertex G) ⟶ TwistedArrow C :=
  (TwistedArrow A ◁ vertexFiberι (twistedArrowProjection ((ihom A).obj C))
    (SSet.opObjEquiv.symm (functorVertex F), functorVertex G)) ≫
      edgewiseInternalHomEvaluation A C

/-- 概要：twisted Hom の評価は元の F と G の両端を厳密に保つ。
方針：左右の評価の公式と、twisted Hom の fiber 条件を各次数で比較する。
規約：対象ごとの同型ではなく底上の射の等式。使われ方：end の切断への持ち上げ。 -/
lemma twistedFunctorHomEvaluation_projection {A C : SSet.{u}} (F G : A ⟶ C) :
    twistedFunctorHomEvaluation F G ≫ twistedArrowProjection C =
      fst _ _ ≫ functorEndPairBase F G := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨a, s⟩
  apply Prod.ext
  · have h := congrArg (fun f ↦ f.app n (a, s.val))
      (edgewiseInternalHomEvaluation_left A C)
    have hs := congrArg Prod.fst s.property
    change (edgewiseLeft ((ihom A).obj C)).app n s.val =
      PinchedHom.constant (SSet.opObjEquiv.symm (functorVertex F)) n.unop.len at hs
    change (edgewiseLeft C).app n ((edgewiseInternalHomEvaluation A C).app n (a, s.val)) =
      (oppositeInternalHomEvaluation A C).app n
        ((edgewiseLeft A).app n a, (edgewiseLeft ((ihom A).obj C)).app n s.val) at h
    rw [hs] at h
    exact h
  · have h := congrArg (fun f ↦ f.app n (a, s.val))
      (edgewiseInternalHomEvaluation_right A C)
    have hs := congrArg Prod.snd s.property
    change (edgewiseRight ((ihom A).obj C)).app n s.val =
      PinchedHom.constant (functorVertex G) n.unop.len at hs
    change (edgewiseRight C).app n ((edgewiseInternalHomEvaluation A C).app n (a, s.val)) =
      ((ihom.ev A).app C).app n
        ((edgewiseRight A).app n a, (edgewiseRight ((ihom A).obj C)).app n s.val) at h
    rw [hs] at h
    exact h

/-- 概要：指定した二関手の end 係数を分類する全空間。
方針：twisted arrow の Hom 射影を両端の底写像で引き戻す。
規約：全空間の模型を実際の pullback に固定する。
使われ方：写像空間の end 表示を切断空間で検証する。 -/
def functorEndTotal {A C : SSet.{u}} (F G : A ⟶ C) : SSet.{u} :=
  pullback (twistedArrowProjection C) (functorEndPairBase F G)

/-- 概要：end 係数の全空間から元の twisted arrow 添字への射影。
方針：引き戻しの第二射影を使う。
規約：元の F と G を保持する。使われ方：end の切断空間の底写像。 -/
def functorEndProjection {A C : SSet.{u}} (F G : A ⟶ C) :
    functorEndTotal F G ⟶ TwistedArrow A :=
  pullback.snd (twistedArrowProjection C) (functorEndPairBase F G)

/-- 概要：end 係数の射影は標的が quasicategory なら left fibration。
方針：元の twisted arrow 射影の left fibration 性を pullback で移す。
規約：始域の quasicategory 性は不要。使われ方：切断空間の Kan 性と極限表示。 -/
instance functorEndProjection_leftFibration {A C : SSet.{u}} [Quasicategory C]
    (F G : A ⟶ C) : LeftFibration (functorEndProjection F G) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := twistedArrowProjection C))⟩

/-- 概要：end の全空間の分類図式は元の共同 Hom の両端制限と全自然同型。
方針：twisted arrow 射影の分類の底変換同型を適用する。
規約：固定した F と G について添字全体の自然性を保持する。
使われ方：end 係数と切断空間による極限の比較。 -/
def functorEndProjection_classificationIso {A C : SSet.{u}} [Quasicategory C]
    (F G : A ⟶ C) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (functorEndPairBase F G) ≫ twistedArrowHomInfinity C)
      (leftStraighteningInfinityDiagram (functorEndProjection F G)) :=
  leftStraighteningInfinityDiagram_baseChangeIso (twistedArrowProjection C) (functorEndPairBase F G)

/-- 概要：関手圏の twisted Hom の各パラメーターは end の切断を定める。
方針：普遍評価を両端の固定条件で全空間へ持ち上げる。
規約：全パラメーターで一つの射を構成する。使われ方：切断比較の uncurry。 -/
def twistedFunctorHomEndEvaluation {A C : SSet.{u}} (F G : A ⟶ C) :
    TwistedArrow A ⊗ twistedArrowHomSpace (functorVertex F) (functorVertex G) ⟶
      functorEndTotal F G :=
  pullback.lift (twistedFunctorHomEvaluation F G) (fst _ _)
    (twistedFunctorHomEvaluation_projection F G)

/-- 概要：元の関手圏の twisted Hom から end 係数の切断空間への実比較射。
方針：両端を固定した普遍評価を切断空間の表現性で curry する。
規約：この宣言だけでは同値性を主張しない。
使われ方：P-12 の写像空間の極限表示の比較射。 -/
def twistedFunctorHomToEndSections {A C : SSet.{u}} (F G : A ⟶ C) :
    twistedArrowHomSpace (functorVertex F) (functorVertex G) ⟶
      HomotopyLimits.simplicialSections (functorEndProjection F G) :=
  HomotopyLimits.simplicialSectionsLift (twistedFunctorHomEndEvaluation F G)
    (pullback.lift_snd _ _ _)

/-- 概要：実比較射を普遍的な切断で評価すると元の twisted Hom の評価に戻る。
方針：切断空間への持ち上げの評価則を使う。
規約：全パラメーターの射の等式。使われ方：比較射の同値性と自然性の検証。 -/
lemma twistedFunctorHomToEndSections_evaluation {A C : SSet.{u}} (F G : A ⟶ C) :
    (TwistedArrow A ◁ twistedFunctorHomToEndSections F G) ≫
      HomotopyLimits.simplicialSectionsEvaluation (functorEndProjection F G) =
        twistedFunctorHomEndEvaluation F G :=
  HomotopyLimits.simplicialSectionsLift_evaluation _ _

end SerrePositivity.InfinityCategories.F2.Presentable

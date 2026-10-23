module

public import SerrePositivity.InfinityCategories.F1.LeftScaffold
public import SerrePositivity.InfinityCategories.Core.VertexFiberNervePullback
public import SerrePositivity.InfinityCategories.F1.SimplicialReplacementBaseChange

/-!
概要：通常の圏の関手による left scaffold の底変換。
方針：比較射を引き戻しへ持ち上げ、各係数値の比較を fiber の標準同型で元へ戻す。
規約：底変換は pullback.snd p (nerveMap H) とする。
使われ方：Kerodon Remark 5.3.2.3、Theorem 5.3.5.7、底の各標準単体上への還元。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：left fibration の通常の nerve の関手による引き戻しは left fibration。
方針：左ホーンの右持ち上げ性の底変換での閉性を使う。
規約：射影は引き戻しの第二射影。
使われ方：Kerodon §5.1.4、scaffold の底変換の値域。 -/
instance leftFibration_nervePullback
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) [LeftFibration p] (H : D ⥤ C) :
    LeftFibration (pullback.snd p (nerveMap H)) :=
  ⟨leftFibrations.pullback_snd p (nerveMap H) (LeftFibration.mem (p := p))⟩

/-- 概要：係数値の定値包含は通常の関手による底変換と可換。
方針：定値射列の後合成が像の対象の定値射列になることを関手の恒等則で示す。
規約：係数単体は同じ射を使う。
使われ方：Kerodon Remark 5.3.2.3、底変換した scaffold の fiber 比較。 -/
lemma simplicialReplacementConstantLift_baseMap
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ SSet.{u}) (d : D) :
    simplicialReplacementConstantLift (H ⋙ F) d ≫ simplicialReplacementBaseMap H F =
      simplicialReplacementConstantLift F (H.obj d) := by
  apply SSet.hom_ext
  intro k
  apply ConcreteCategory.hom_ext
  intro s
  have hσ : (CategoryTheory.Functor.const (Fin (k.unop.len + 1))).obj d ⋙ H =
      (CategoryTheory.Functor.const (Fin (k.unop.len + 1))).obj (H.obj d) := by
    refine CategoryTheory.Functor.ext (fun _ ↦ rfl) ?_
    intro i j f
    simp
  exact Sigma.ext hσ (HEq.rfl)

/-- 概要：底を保つ simplicial replacement の比較射を新しい底へ引き戻す。
方針：元の比較射と新しい底の射影を引き戻しの普遍性で組にする。
規約：h は元の比較射の底上の可換性。
使われ方：Kerodon Remark 5.3.2.3、scaffold の底変換の比較射。 -/
noncomputable def leftScaffoldBaseChange
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (H : D ⥤ C) :
    simplicialReplacement (H ⋙ F) ⟶ pullback p (nerveMap H) :=
  pullback.lift (simplicialReplacementBaseMap H F ≫ l) (simplicialReplacementProjection (H ⋙ F))
    (by rw [Category.assoc, h, simplicialReplacementBaseMap_projection])

/-- 概要：底変換した比較射は新しい底の nerve 上の射。
方針：引き戻しの持ち上げの第二射影の計算則を使う。
規約：底変換した係数図式は H⋙F。
使われ方：Kerodon Theorem 5.3.5.7、単体上の scaffold の底の条件。 -/
lemma leftScaffoldBaseChange_projection
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (H : D ⥤ C) :
    leftScaffoldBaseChange p F l h H ≫ pullback.snd p (nerveMap H) =
      simplicialReplacementProjection (H ⋙ F) := pullback.lift_snd _ _ _

/-- 概要：底変換した比較射の fiber 射は標準 fiber 同型を通すと元の係数の比較射となる。
方針：元の全空間への包含で比較し、引き戻しの第一射影と定値包含の自然性を計算する。
規約：fiber の同型は nerve の頂点の表示も揃える標準同型。
使われ方：Kerodon Theorem 5.3.5.7、底変換した scaffold の同値条件。 -/
lemma leftScaffoldBaseChange_fiber
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    (p : E ⟶ nerve C) (F : C ⥤ SSet.{u}) (l : simplicialReplacement F ⟶ E)
    (h : l ≫ p = simplicialReplacementProjection F) (H : D ⥤ C) (d : D) :
    leftScaffoldFiberMap (pullback.snd p (nerveMap H)) (H ⋙ F) (leftScaffoldBaseChange p F l h H)
        (leftScaffoldBaseChange_projection p F l h H) d ≫ (vertexFiberNervePullbackIso p H d).hom =
      leftScaffoldFiberMap p F l h (H.obj d) := by
  apply vertexFiber_hom_ext
  rw [Category.assoc, vertexFiberNervePullbackIso_hom_ι, ← Category.assoc]
  change (simplicialReplacementConstantLift (H ⋙ F) d ≫ leftScaffoldBaseChange p F l h H) ≫
      pullback.fst p (nerveMap H) = simplicialReplacementConstantLift F (H.obj d) ≫ l
  dsimp only [leftScaffoldBaseChange]
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
    simplicialReplacementConstantLift_baseMap]

/-- 概要：left scaffold の条件は通常の関手による底変換で保存される。
方針：係数値の fiber 比較の可換式と標準 fiber 同型を使い、同値の二三性で判定する。
規約：係数値は Kan、射影は left fibration。
使われ方：Kerodon Theorem 5.3.5.7、底を通常の有限順序へ還元する操作。 -/
lemma IsLeftScaffold.baseChange
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E : SSet.{u}}
    {p : E ⟶ nerve C} [LeftFibration p] {F : C ⥤ SSet.{u}} [∀ c, KanComplex (F.obj c)]
    {l : simplicialReplacement F ⟶ E} (hs : IsLeftScaffold p F l) (H : D ⥤ C) :
    ∃ h : l ≫ p = simplicialReplacementProjection F,
      @IsLeftScaffold D _ _ (pullback.snd p (nerveMap H)) inferInstance (H ⋙ F)
        (fun d ↦ inferInstanceAs (KanComplex (F.obj (H.obj d))))
        (leftScaffoldBaseChange p F l h H) := by
  have (d : D) : KanComplex ((H ⋙ F).obj d) :=
    inferInstanceAs (KanComplex (F.obj (H.obj d)))
  rcases hs with ⟨h, hf⟩
  refine ⟨h, leftScaffoldBaseChange_projection p F l h H, fun d ↦ ?_⟩
  have he := (qCatEquivalenceOfIso (vertexFiberNervePullbackIso p H d)).isQCatEquivalence
  apply he.cancel_right
  change IsQCatEquivalence (leftScaffoldFiberMap (pullback.snd p (nerveMap H)) (H ⋙ F)
    (leftScaffoldBaseChange p F l h H) (leftScaffoldBaseChange_projection p F l h H) d ≫
      (vertexFiberNervePullbackIso p H d).hom)
  rw [leftScaffoldBaseChange_fiber]
  exact hf (H.obj d)

end SerrePositivity.InfinityCategories

module
public import SerrePositivity.KST.SConstruction.EdgeTargetColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitAttachment

/-! # 恒等辺を持つ span の余極限
概要：恒等射を一方の脚とする span の余極限性を、もう一方の辺に制限して判定する。
方針：一点図式の恒等余錐を span に付加し、余極限付加補題を用いる。
規約：固定図式の射の等号を保持する。使われ方：第一行と対角の厳密な補完。
原典：HTT §1.2.12・§4.3.2、BGT Lemma 7.3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：span は第一の辺に、共通始点から第二の辺を付加した pushout。
方針：一次元の標準 join 同型をホーンの pushout に適用する。
規約：付加する辺は 0→2、残す辺は 0→1。使われ方：恒等脚の余極限付加。 -/
lemma identityLegAttachment_isPushout :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0]) (stdSimplex.δ (1 : Fin 2))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₂) horn₂₀.ι₀₁ := by
  apply horn₂₀.isPushout.flip.of_iso' (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0)
    (Iso.refl _) (Iso.refl _)
  · apply SSet.yonedaEquiv.injective
    decide
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- 概要：第二の脚が厳密な恒等射である span の余錐は、第一の辺への制限で余極限性を判定できる。
方針：一点の恒等余錐の普遍性と余極限付加による制限の同値を使う。
規約：恒等脚の条件は join による余錐の表示で指定する。
使われ方：第一行で恒等辺を持つ押し出しの証明。 -/
lemma isColimitCone_iff_restrict_of_identity_leg {C : SSet.{u}} [Quasicategory C]
    {p : (horn 2 0 : SSet.{u}) ⟶ C} (a : (Δ[0] : SSet.{u}) ⟶ C)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₂ ≫ p = (identityCocone a).val)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict horn₂₀.ι₀₁) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_colimit_attachment (identityCocone a)
    (identityCocone_isColimit a) (stdSimplex.δ (1 : Fin 2))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₂) horn₂₀.ι₀₁
    identityLegAttachment_isPushout (by simpa only [Category.assoc] using hp) c


/-- 概要：正方形を第一座標へ射影した余錐の第一辺への制限は、辺の終点の余錐。
方針：二三角形による標準同型の第一成分を計算する。
規約：第一座標は水平方向。使われ方：恒等垂直辺を持つ押し出し。 -/
lemma spanCoconeSquare_fst_restrict :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₁ (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫
      CartesianMonoidalCategory.fst _ _ = edgeTargetShape := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv).1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫
    CartesianMonoidalCategory.fst _ _ = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left]
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：任意の辺を第一座標で引き戻した正方形は押し出し。
方針：第二の脚が恒等であることから第一辺に制限し、終点の余極限性を使う。
規約：値域は quasicategory。使われ方：第一行の cofiber 四角形の厳密な指定。 -/
lemma isPushoutSquare_fst {C : SSet.{u}} [Quasicategory C]
    (F : (Δ[1] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (CartesianMonoidalCategory.fst _ _ ≫ F) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (CartesianMonoidalCategory.fst _ _ ≫ F))
  apply (isColimitCone_iff_restrict_of_identity_leg
    (stdSimplex.δ (1 : Fin 2) ≫ F) ?_ _).2
  · apply (isColimitCone_iff_of_map_eq _ (edgeTargetCocone F) ?_).2
      (edgeTargetCocone_isColimit F)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₁ (𝟙 (Δ[0] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (CartesianMonoidalCategory.fst _ _ ≫ F)) =
      edgeTargetShape ≫ F
    simpa only [Category.assoc] using congrArg (fun f => f ≫ F)
      spanCoconeSquare_fst_restrict
  · rw [identityCocone_val]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₂ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ (CartesianMonoidalCategory.fst _ _ ≫ F)) = _
    rw [← Category.assoc horn₂₀.ι₀₂, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ CartesianMonoidalCategory.fst _ _ =
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
      exact CartesianMonoidalCategory.lift_fst _ _
    rw [← Category.assoc _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge, he, SSet.const_comp, SSet.comp_const]
    congr 1
    change F.app (Opposite.op ⦋0⦌) _ = SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ F)
    rw [SSet.yonedaEquiv_comp]
    congr 1
    decide

/-- 概要：span は第二の辺に、共通始点から第一の辺を付加した pushout。
方針：一次元の標準 join 同型をホーンの pushout に適用する。
規約：付加する辺は 0→1、残す辺は 0→2。使われ方：恒等脚の余極限付加。 -/
lemma identityFirstLegAttachment_isPushout :
    IsPushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0]) (stdSimplex.δ (1 : Fin 2))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁) horn₂₀.ι₀₂ := by
  apply horn₂₀.isPushout.of_iso' (Iso.refl _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0)
    (Iso.refl _) (Iso.refl _)
  · apply SSet.yonedaEquiv.injective
    decide
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

/-- 概要：第一の脚が厳密な恒等射である span の余錐は、第二の辺への制限で余極限性を判定できる。
方針：一点の恒等余錐の普遍性と余極限付加による制限の同値を使う。
規約：恒等脚の条件は join による余錐の表示で指定する。
使われ方：第一行で恒等辺を持つ押し出しの証明。 -/
lemma isColimitCone_iff_restrict_of_identity_first_leg {C : SSet.{u}} [Quasicategory C]
    {p : (horn 2 0 : SSet.{u}) ⟶ C} (a : (Δ[0] : SSet.{u}) ⟶ C)
    (hp : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁ ≫ p = (identityCocone a).val)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict horn₂₀.ι₀₂) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_colimit_attachment (identityCocone a)
    (identityCocone_isColimit a) (stdSimplex.δ (1 : Fin 2))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁) horn₂₀.ι₀₂
    identityFirstLegAttachment_isPushout (by simpa only [Category.assoc] using hp) c


/-- 概要：正方形を第二座標へ射影した余錐の第二辺への制限は、辺の終点の余錐。
方針：二三角形による標準同型の第二成分を計算する。
規約：第二座標は垂直方向。使われ方：恒等水平辺を持つ押し出し。 -/
lemma spanCoconeSquare_snd_restrict :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₂ (𝟙 (Δ[0] : SSet.{u})) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫
      CartesianMonoidalCategory.snd _ _ = edgeTargetShape := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).inv).1
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫
    CartesianMonoidalCategory.snd _ _ = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right]
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：任意の辺を第二座標で引き戻した正方形は押し出し。
方針：第一の脚が恒等であることから第二辺に制限し、終点の余極限性を使う。
規約：値域は quasicategory。使われ方：第一行の cofiber 四角形の厳密な指定。 -/
lemma isPushoutSquare_snd {C : SSet.{u}} [Quasicategory C]
    (F : (Δ[1] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (CartesianMonoidalCategory.snd _ _ ≫ F) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone (CartesianMonoidalCategory.snd _ _ ≫ F))
  apply (isColimitCone_iff_restrict_of_identity_first_leg
    (stdSimplex.δ (1 : Fin 2) ≫ F) ?_ _).2
  · apply (isColimitCone_iff_of_map_eq _ (edgeTargetCocone F) ?_).2
      (edgeTargetCocone_isColimit F)
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap horn₂₀.ι₀₂ (𝟙 (Δ[0] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ (CartesianMonoidalCategory.snd _ _ ≫ F)) =
      edgeTargetShape ≫ F
    simpa only [Category.assoc] using congrArg (fun f => f ≫ F)
      spanCoconeSquare_snd_restrict
  · rw [identityCocone_val]
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ horn₂₀.ι₀₁ ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary ≫ (CartesianMonoidalCategory.snd _ _ ≫ F)) = _
    rw [← Category.assoc horn₂₀.ι₀₁, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_bottomEdge]
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ CartesianMonoidalCategory.snd _ _ =
        SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
      exact CartesianMonoidalCategory.lift_snd _ _
    rw [← Category.assoc _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge, he, SSet.const_comp, SSet.comp_const]
    congr 1
    change F.app (Opposite.op ⦋0⦌) _ = SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 2) ≫ F)
    rw [SSet.yonedaEquiv_comp]
    congr 1
    decide

end SerrePositivity.KST.SConstruction

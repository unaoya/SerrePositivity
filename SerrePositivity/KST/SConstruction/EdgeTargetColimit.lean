module
public import SerrePositivity.KST.SConstruction.IdentityCocones
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-! # 標準辺の終点を余極限とする余錐
概要：射の図式の終点に恒等辺を付けた余錐は余極限である。
方針：最後の頂点の right anodyne 性で一点図式の恒等余錐に制限する。
規約：Core・Stable の公開宣言は変更しない。使われ方：恒等辺を持つ押し出し。
原典：HTT §1.2.12・§4.3.2、BGT Lemma 7.3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：一次ホーンの最後の頂点は標準辺の最後の面。
方針：ホーンの面の上限表示の唯一の添字を取る。
規約：除外する頂点は1。使われ方：終点包含の right anodyne 性。 -/
lemma horn_one_one_eq_last_face :
    (horn 1 1 : (Δ[1] : SSet.{u}).Subcomplex) = stdSimplex.face {(0 : Fin 2)}ᶜ := by
  rw [horn_eq_iSup]
  apply le_antisymm
  · apply iSup_le
    rintro ⟨j, hj⟩
    fin_cases j
    · exact le_rfl
    · exact (hj rfl).elim
  · exact le_iSup_of_le ⟨0, by decide⟩ le_rfl

/-- 概要：標準辺の最後の頂点の包含は right anodyne。
方針：一次ホーンの包含と面の標準単体同型を合成する。
規約：射は δ₀。使われ方：射の終点による余極限の判定。 -/
lemma lastVertex_rightAnodyne : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (stdSimplex.δ (0 : Fin 2) :
    (Δ[0] : SSet.{u}) ⟶ Δ[1]) := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (stdSimplex.face {(0 : Fin 2)}ᶜ).ι := by
    rw [← horn_one_one_eq_last_face]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions_horn (1 : Fin 2) (by decide)
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions.comp_mem
    (stdSimplex.faceSingletonComplIso (0 : Fin 2)).hom _
    (MorphismProperty.of_isIso _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions _) h
  simpa only [stdSimplex.faceSingletonComplIso_hom_ι] using hi

/-- 概要：辺に終点の恒等射を付ける右余錐の形状。
方針：辺と点の join を三角形にし、最後の二頂点を同一視する。
規約：σ₁ は頂点1を重複させる。使われ方：射の終点の余極限余錐。 -/
def edgeTargetShape : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet.{u}) Δ[0] ⟶ Δ[1] :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ (1 : Fin 2)

/-- 概要：辺の右余錐の形状は元の辺で恒等。
方針：最初の辺は δ₂、σ₁ との合成は恒等となる。
規約：形状の厳密な等号。使われ方：余錐の固定条件。 -/
lemma edgeTargetShape_inl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] : SSet.{u}) Δ[0] ≫ edgeTargetShape = 𝟙 _ := by
  rw [edgeTargetShape, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.joinStdSimplexIso_one_zero_inl]
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：辺の右余錐を最後の頂点に制限すると終点への定値射となる。
方針：点と点の join を標準辺に直して有限頂点写像を計算する。
規約：余錐の頂点も終点。使われ方：一点図式の恒等余錐への帰着。 -/
lemma edgeTargetShape_restrict_last :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (Δ[0] : SSet.{u})) ≫ edgeTargetShape =
      SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv).1
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：射の終点に恒等辺を付けた余錐。
方針：終点を繰り返す三角形の形状で前合成する。
規約：元の図式は標準辺上の F。使われ方：退化した押し出しの比較余錐。 -/
def edgeTargetCocone {C : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F :=
  ⟨edgeTargetShape ≫ F, by rw [← Category.assoc, edgeTargetShape_inl, Category.id_comp]⟩

/-- 概要：射の終点はその射の図式の余極限である。
方針：right anodyne な終点への制限で、恒等余錐の普遍性に帰着する。
規約：C は quasicategory。使われ方：恒等辺を持つ普遍四角形の構成。 -/
lemma edgeTargetCocone_isColimit {C : SSet.{u}} [Quasicategory C]
    (F : (Δ[1] : SSet.{u}) ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (edgeTargetCocone F) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_rightAnodyne (edgeTargetCocone F)
    (stdSimplex.δ (0 : Fin 2)) lastVertex_rightAnodyne).2
  apply pointCocone_isColimit_of_constant _ (F.app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (𝟙 (Δ[0] : SSet.{u})) ≫ (edgeTargetShape ≫ F) = _
  rw [← Category.assoc, edgeTargetShape_restrict_last, SSet.const_comp]

end SerrePositivity.KST.SConstruction

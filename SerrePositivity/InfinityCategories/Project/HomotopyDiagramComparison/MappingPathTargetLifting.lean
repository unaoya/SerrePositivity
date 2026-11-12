module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.F1PointedAcyclicFibrationLifting
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FreeInterval
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PullbackKanSequence
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.MappingPathNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.MappingPathSourceLifting
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.RelativeFreePathBoundary
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopyIsomorphism
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreePathSpace
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.MappingPathSpace
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.MonoRightHomotopyEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.PointedKanWhitehead
public import SerrePositivity.Spectra.Pointed.InternalHom
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：mapping path の標的射影の相対比較の持ち上げ性。
方針：源成分を先に持ち上げ、底の path と両端点を保つ相対充填で貼り合わせる。
規約：元の正方形の両縦射の fibration 性を用いる。
使われ方：Goerss–Jardine I §7、HTT A.3.3、Sp の塔の極限の π_* 比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 概要：mapping path の標的射影の相対比較射。
方針：次段の標的成分と前段の mapping path を引き戻しへまとめる。
規約：標的は基礎単体集合の引き戻し。
使われ方：標的への塔の射の matching map の具体的表示。 -/
def mappingPathTargetMatchingMap {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f).right ⟶ pullback b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right :=
  pullback.lift (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f).right (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap f f' a b h).right (by
    simpa only [Under.comp_right] using
      congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap_target f f' a b h).symm)

/-- 概要：両縦射が fibration なら標的射影の相対比較も fibration。
方針：源のホーンを縦射に沿って充填し、path の両端点を固定して相対充填する。
規約：各対象の Kan 性と横射の π_* 同型性は不要。
使われ方：段ごとの π_* 同型から塔の相対比較の全ての単射への RLP を導く。 -/
lemma mappingPathTargetMatchingMap_fibration {X Y X' Y' : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') [Fibration a.right] [Fibration b.right] :
    Fibration (mappingPathTargetMatchingMap f f' a b h) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro T U j hj
  have : HasLiftingProperty j a.right :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance j hj
  constructor
  intro t u sq
  let uY := u ≫ pullback.fst b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right
  let uM := u ≫ pullback.snd b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right
  have ht : t ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f).right = j ≫ uY := by
    have he := congrArg (fun k : T ⟶ pullback b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right ↦
      k ≫ pullback.fst b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right) sq.w
    simpa only [Category.assoc, mappingPathTargetMatchingMap, pullback.lift_fst, uY] using he
  have hm : t ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap f f' a b h).right = j ≫ uM := by
    have he := congrArg (fun k : T ⟶ pullback b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right ↦
      k ≫ pullback.snd b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right) sq.w
    simpa only [Category.assoc, mappingPathTargetMatchingMap, pullback.lift_snd, uM] using he
  let pb := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f
  let pb' := _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedPullback_isPullback (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f'
  have hpb : (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right ≫ f.right := pb.w
  have hpb' : (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f').right ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1).right = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right ≫ f'.right := pb'.w
  have hpath := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap_path f f' a b h)
  have hsource := congrArg Under.Hom.right (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap_source f f' a b h)
  have hv := congrArg Under.Hom.right h
  simp only [Under.comp_right] at hpath hsource hv
  let sqX : CommSq (t ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right) j a.right
      (uM ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right) := ⟨by
    rw [Category.assoc, ← hsource, ← Category.assoc, hm, Category.assoc]⟩
  have hu : uY ≫ b.right = uM ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (u ≫ ·) pullback.condition).trans (Category.assoc _ _ _).symm)
  have hc₀ : j ≫ uY = (t ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0).right := ht.symm
  have hc₁ : j ≫ (sqX.lift ≫ f.right) =
      (t ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1).right := by
    rw [← Category.assoc, sqX.fac_left, Category.assoc, ← hpb, ← Category.assoc]
  have he : (t ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right) ≫
      (PointedObject.basedHomMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeInterval.{u} b).right =
        j ≫ (uM ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f').right) := by
    rw [Category.assoc, ← hpath, ← Category.assoc, hm, Category.assoc]
  have ha₀ : uY ≫ b.right = (uM ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f').right) ≫
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 0).right := hu
  have ha₁ : (sqX.lift ≫ f.right) ≫ b.right =
      (uM ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f').right) ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1).right := by
    rw [Category.assoc, hv, ← Category.assoc, sqX.fac_right,
      Category.assoc, ← hpb', ← Category.assoc]
  obtain ⟨v, hjv, hend₀, hend₁, hbase⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeFreePath_boundaryHornLift b j hj
    (t ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right) uY (sqX.lift ≫ f.right)
    (uM ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y' 1) f').right) hc₀ hc₁ he ha₀ ha₁
  let l := pb.lift v sqX.lift hend₁
  have hls : l ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right = sqX.lift := pb.lift_snd _ _ _
  have hlp : l ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right = v := pb.lift_fst _ _ _
  refine ⟨⟨{ l := l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · apply pb.hom_ext
    · rw [Category.assoc, hlp]
      exact hjv
    · change (j ≫ l) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f).right = _
      rw [Category.assoc, hls]
      exact sqX.fac_left
  · apply pullback.hom_ext
    · simp only [Category.assoc, mappingPathTargetMatchingMap, pullback.lift_fst]
      change l ≫ (pullback.fst (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 1) f).right ≫
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint Y 0).right = uY
      rw [← Category.assoc, hlp]
      exact hend₀
    · simp only [Category.assoc, mappingPathTargetMatchingMap, pullback.lift_snd]
      change l ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap f f' a b h).right = uM
      apply pb'.hom_ext
      · rw [Category.assoc, hpath, ← Category.assoc, hlp]
        exact hbase
      · change (l ≫ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.mappingPathMap f f' a b h).right) ≫
          (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right = uM ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathRetraction f').right
        rw [Category.assoc, hsource, ← Category.assoc, hls]
        exact sqX.fac_right

/-- 概要：両横射が π_* 同型なら標的射影の相対比較は全ての単射への RLP を持つ。
方針：前段の標的射影の引き戻しと次段の標的射影を比較し、相対 Whitehead を適用する。
規約：四つの対象の Kan 性、両縦射の fibration 性、両横射の全基点 π_* 同型性を要求する。
使われ方：mapping path の塔から標的への極限の射の持ち上げ性。 -/
lemma mappingPathTargetMatchingMap_rlp {X Y X' Y' : PointedSimplicialSet.{u}}
    [KanComplex X.right] [KanComplex Y.right] [KanComplex X'.right] [KanComplex Y'.right]
    (f : X ⟶ Y) (f' : X' ⟶ Y') (a : X ⟶ X') (b : Y ⟶ Y')
    (h : f ≫ b = a ≫ f') [Fibration a.right] [Fibration b.right]
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f.right) (hf' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f'.right) :
    (MorphismProperty.monomorphisms SSet.{u}).rlp (mappingPathTargetMatchingMap f f' a b h) := by
  have : Fibration (mappingPathTargetMatchingMap f f' a b h) :=
    mappingPathTargetMatchingMap_fibration f f' a b h
  have : KanComplex (pullback b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pullback_kanComplex_of_fibration b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right
  have hp : (MorphismProperty.monomorphisms SSet.{u}).rlp
      (pullback.fst b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right) :=
    (MorphismProperty.rlp _).pullback_fst _ _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_rlp_of_piIsomorphism f' hf')
  have he : mappingPathTargetMatchingMap f f' a b h ≫
      pullback.fst b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right = (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f).right :=
    pullback.lift_fst ..
  have hm : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (mappingPathTargetMatchingMap f f' a b h) := by
    apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := pullback.fst b.right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPathProjection f').right)
      _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight _ hp)
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mappingPathProjection_piIsomorphism f hf
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_rlp_of_piIsomorphism _ hm (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.mappingPath f).basepoint

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

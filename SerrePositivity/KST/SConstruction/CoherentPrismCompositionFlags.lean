module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CoherentStringPrismChains
public import SerrePositivity.KST.SConstruction.CoherentStringDiagramCells
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.CoherentStringPathFlags
public import SerrePositivity.KST.SConstruction.CoherentPathMappingHomotopy

/-! # 上下の全精密化の Path は元の合成面を通る
概要：上下の全精密化の Path 単体が、縦辺との切断点を全頂点で通ることを証明する。
方針：元の再添字の始点・終点保持を使い、元の豊穣合成則をそのまま評価する。
規約：全高次パラメータを保ち、合成円柱の存在や Kan 性を仮定しない。
使われ方：上下の native Hom 族の終点を、水平部分と縦辺の二合成へ厳密に分割する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I : Type u} [SmallCategory I] {x y : I} {f : x ⟶ y}

/-- 下側の全精密化の Path は、元の終点の直後の縦辺との切断点を通る。 -/
lemma coherentLowerPrismRefinementPath_cut {s t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f} (a : s ⟶ t) :
    (ULift.up (Fin.last t.length).castSucc : ULift.{u} (Fin (t.length + 2))) ∈
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringMap a)).I := by
  refine ⟨(Fin.last s.length).castSucc, ?_⟩
  change ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend a.map).toOrderHom
    (Fin.last s.length).castSucc) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerStringExtend_castSucc, a.last]

/-- 上側の全精密化の Path は、元の始点の縦辺の直後の切断点を通る。 -/
lemma coherentUpperPrismRefinementPath_cut {s t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f} (a : s ⟶ t) :
    (ULift.up ((0 : Fin (t.length + 1)).succ) : ULift.{u} (Fin (t.length + 2))) ∈
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringRefinementPath (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringMap a)).I := by
  refine ⟨(0 : Fin (s.length + 1)).succ, ?_⟩
  change ULift.up ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend a.map).toOrderHom
    (0 : Fin (s.length + 1)).succ) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperStringExtend_succ, a.first]

/-- 下側の全高次精密化の単体は、元の合成面に厳密に属する。 -/
lemma coherentLowerPrismPathFlag_through {d : ℕ}
    (F : (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) _⦋d⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (F ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (ULift.up (Fin.last (F.obj (Fin.last d)).length).castSucc)).obj
        (Opposite.op ⦋d⦌) := by
  intro k
  exact coherentLowerPrismRefinementPath_cut (F.map (homOfLE (Fin.le_last k)))

/-- 上側の全高次精密化の単体も、元の合成面に厳密に属する。 -/
lemma coherentUpperPrismPathFlag_through {d : ℕ}
    (F : (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) _⦋d⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (F ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f) ∈
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough
        (ULift.up ((0 : Fin ((F.obj (Fin.last d)).length + 1)).succ))).obj
          (Opposite.op ⦋d⦌) := by
  intro k
  exact coherentUpperPrismRefinementPath_cut (F.map (homOfLE (Fin.le_last k)))

/-- 合成面の元の高次 Path 評価は、元の前半・後半の豊穣作用の実合成そのもの。 -/
lemma coherentPathFlag_mapping_comp {J : Type u} [LinearOrder J] {a b c : J}
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : EnrichedFunctor SSet.{u} (SimplicialThickening J) C)
    (hab : a ≤ b) (hbc : b ≤ c) {d : ℕ} (P : (nerve (Path a c)) _⦋d⦌)
    (hP : P ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough b).obj (Opposite.op ⦋d⦌)) :
    (s.map (.mk a) (.mk c)).app (Opposite.op ⦋d⦌) P =
      (coherentPathCutSplit hab hbc ≫
        (s.map (.mk a) (.mk b) ⊗ₘ s.map (.mk b) (.mk c)) ≫
          eComp SSet (s.obj (.mk a)) (s.obj (.mk b)) (s.obj (.mk c))).app
            (Opposite.op ⦋d⦌) P := by
  have hi : (nerveMap (coherentPathInsertFunctor hab hbc)).app (Opposite.op ⦋d⦌) P = P := by
    refine CategoryTheory.Functor.ext (fun k => coherentPathInsert_eq hab hbc _ (hP k)) ?_
    intro i j q
    apply InducedCategory.hom_ext
    exact Subsingleton.elim _ _
  have h := congrArg (fun m => m.app (Opposite.op ⦋d⦌) P)
    (coherentPathCutSplit_mapping s hab hbc)
  change (s.map (.mk a) (.mk c)).app _
    ((nerveMap (coherentPathInsertFunctor hab hbc)).app _ P) = _ at h
  rw [hi] at h
  exact h

/-- 元の図式の下側の全パラメータの評価を、同じ元の豊穣作用の実合成へ分割する。 -/
lemma coherentLowerPrismPathFlag_mapping_comp
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {d : ℕ} (F : (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) _⦋d⦌) :
    let t := F.obj (Fin.last d)
    let s := coherentStringDiagramCell Q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString t).chain
    let a : ULift.{u} (Fin (t.length + 2)) := ULift.up 0
    let b : ULift.{u} (Fin (t.length + 2)) := ULift.up (Fin.last t.length).castSucc
    let c : ULift.{u} (Fin (t.length + 2)) := ULift.up (Fin.last (t.length + 1))
    let P := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (F ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f)
    (s.map (.mk a) (.mk c)).app (Opposite.op ⦋d⦌) P =
      (coherentPathCutSplit (show a ≤ b from Fin.zero_le _) (show b ≤ c from Fin.le_last _) ≫
        (s.map (.mk a) (.mk b) ⊗ₘ s.map (.mk b) (.mk c)) ≫
          eComp SSet (s.obj (.mk a)) (s.obj (.mk b)) (s.obj (.mk c))).app
            (Opposite.op ⦋d⦌) P := by
  exact coherentPathFlag_mapping_comp
    (coherentStringDiagramCell Q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismString (F.obj (Fin.last d))).chain)
    (show (ULift.up 0 : ULift.{u} (Fin ((F.obj (Fin.last d)).length + 2))) ≤ _ from Fin.zero_le _)
    (show _ ≤ (ULift.up (Fin.last ((F.obj (Fin.last d)).length + 1)) :
      ULift.{u} (Fin ((F.obj (Fin.last d)).length + 2))) from Fin.le_last _)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (F ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentLowerPrismStringFunctor f))
    (coherentLowerPrismPathFlag_through F)

/-- 元の図式の上側の全パラメータの評価を、同じ元の豊穣作用の実合成へ分割する。 -/
lemma coherentUpperPrismPathFlag_mapping_comp
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve (I × ULift.{u} (Fin 2))) ⟶ SimplicialNerve C)
    {d : ℕ} (F : (nerve (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f)) _⦋d⦌) :
    let t := F.obj (Fin.last d)
    let s := coherentStringDiagramCell Q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString t).chain
    let a : ULift.{u} (Fin (t.length + 2)) := ULift.up 0
    let b : ULift.{u} (Fin (t.length + 2)) := ULift.up ((0 : Fin (t.length + 1)).succ)
    let c : ULift.{u} (Fin (t.length + 2)) := ULift.up (Fin.last (t.length + 1))
    let P := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (F ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f)
    (s.map (.mk a) (.mk c)).app (Opposite.op ⦋d⦌) P =
      (coherentPathCutSplit (show a ≤ b from Fin.zero_le _) (show b ≤ c from Fin.le_last _) ≫
        (s.map (.mk a) (.mk b) ⊗ₘ s.map (.mk b) (.mk c)) ≫
          eComp SSet (s.obj (.mk a)) (s.obj (.mk b)) (s.obj (.mk c))).app
            (Opposite.op ⦋d⦌) P := by
  exact coherentPathFlag_mapping_comp
    (coherentStringDiagramCell Q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismString (F.obj (Fin.last d))).chain)
    (show (ULift.up 0 : ULift.{u} (Fin ((F.obj (Fin.last d)).length + 2))) ≤ _ from Fin.zero_le _)
    (show _ ≤ (ULift.up (Fin.last ((F.obj (Fin.last d)).length + 1)) :
      ULift.{u} (Fin ((F.obj (Fin.last d)).length + 2))) from Fin.le_last _)
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathFlag (F ⋙ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentUpperPrismStringFunctor f))
    (coherentUpperPrismPathFlag_through F)

end SerrePositivity.KST.SConstruction

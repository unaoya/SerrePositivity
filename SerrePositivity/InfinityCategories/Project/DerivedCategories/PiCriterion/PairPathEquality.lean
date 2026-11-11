module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PiPathRelation

/-!
概要：同じ path 上の二つの類の等式を、射の後合成後も両端点間で反映する。
方針：path 射の自然性と端点評価のホモトピー群上の単射性を使う。
規約：二つの類は同じ path 頂点を共有する。
使われ方：二球面の同時検出から、比較射の像での等式を段階へ戻す。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra

/-- 同じ path を共有する二つの類は、任意の後合成後も両端点で同時に等しくなる。 -/
lemma shared_path_map_equality_iff {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    (f : X ⟶ Y) (n : ℕ) (z : (KanPath.object X) _⦋0⦌)
    {x₀ x₁ : X _⦋0⦌}
    (h₀ : (KanPath.evaluation X 0).app _ z = x₀)
    (h₁ : (KanPath.evaluation X 1).app _ z = x₁)
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (KanPath.object X) n z) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 0) h₀ a) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 0) h₀ b) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 1) h₁ a) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 1) h₁ b) := by
  let p := (ihom (Δ[1] : SSet.{u})).map f
  let w := p.app (Opposite.op ⦋0⦌) z
  have hw (t : Fin 2) {x : X _⦋0⦌}
      (hx : (KanPath.evaluation X t).app _ z = x) :
      (KanPath.evaluation Y t).app _ w = f.app _ x := by
    have h := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) z)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.path_evaluation_natural f t)
    change (KanPath.evaluation Y t).app _ w =
      f.app _ ((KanPath.evaluation X t).app _ z) at h
    simpa only [hx] using h
  have hs (t : Fin 2) {x : X _⦋0⦌}
      (hx : (KanPath.evaluation X t).app _ z = x)
      (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (KanPath.object X) n z) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation Y t) (hw t hx)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl c) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X t) hx c) :=
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square p f (KanPath.evaluation X t) (KanPath.evaluation Y t)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.path_evaluation_natural f t) rfl rfl hx (hw t hx) n c
  have he (t : Fin 2) {x : X _⦋0⦌}
      (hx : (KanPath.evaluation X t).app _ z = x) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X t) hx a) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X t) hx b)) ↔
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl b := by
    rw [← hs t hx a, ← hs t hx b]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism n (KanPath.evaluation Y t)
      (KanPath.evaluation_piIsomorphism Y t) (hw t hx)).injective.eq_iff
  exact (he 0 h₀).trans (he 1 h₁).symm

/-- 基点を固定しないホモトピーでも、同じ基点の二つの類を同一視する条件は不変。 -/
lemma homotopy_map_equality_iff {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {f g : X ⟶ Y} (H : Homotopy f g) (n : ℕ) (x : X _⦋0⦌)
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl b ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g rfl a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map g rfl b := by
  let t := KanPath.transpose H
  let z := t.app (Opposite.op ⦋0⦌) x
  have he (i : Fin 2) (r : X ⟶ Y) (hr : t ≫ KanPath.evaluation Y i = r) :
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map r (x := x) rfl a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map r rfl b) ↔
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map t rfl a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map t rfl b := by
    have hx : (KanPath.evaluation Y i).app _ z = r.app _ x :=
      congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) x) hr
    have hs (c : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) :
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation Y i) hx
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map t rfl c) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map r rfl c := by
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_id, MonoidHom.id_apply] using
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square t (𝟙 Y) r (KanPath.evaluation Y i)
          (by simpa using hr) rfl rfl rfl hx n c
    rw [← hs a, ← hs b]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_bijective_of_piIsomorphism n (KanPath.evaluation Y i)
      (KanPath.evaluation_piIsomorphism Y i) hx).injective.eq_iff
  exact (he 0 f (KanPath.transpose_zero H)).trans
    (he 1 g (KanPath.transpose_one H)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

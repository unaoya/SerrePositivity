module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion.PathTransport
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.HomotopySquares
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIso

/-!
概要：二つの正次数の類を、指定端点を持つ実際の path 上の一つの類で比較する条件。
方針：path 対象の二端点評価で元を比較し、基点の表示の等号で移送する。
規約：同じ基点でのこの条件を、群の等式と同一視しない。閉路の作用も許す。
使われ方：元ごとの代表元検出と、D の基点移送を含む filtered 条件の界面。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra
variable {X : SSet.{u}} [KanComplex X]

/-- 二端点の類が、同じ実際の path 空間の一つの類から得られる条件。 -/
def PiPathRelated (n : ℕ) {x y : X _⦋0⦌}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y) : Prop :=
  ∃ z : (KanPath.object X) _⦋0⦌,
    ∃ h₀ : (KanPath.evaluation X 0).app _ z = x,
    ∃ h₁ : (KanPath.evaluation X 1).app _ z = y,
    ∃ γ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (KanPath.object X) n z,
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 0) h₀ γ = a ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 1) h₁ γ = b

/-- 基点の表示を等号で変えても、同じ実際の path とその類を使って比較できる。 -/
lemma PiPathRelated.rebase {n : ℕ} {x y x' y' : X _⦋0⦌}
    {a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x} {b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y}
    (h : PiPathRelated n a b) (hx : x = x') (hy : y = y') :
    PiPathRelated n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) hx a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (𝟙 X) hy b) := by
  obtain ⟨z, h₀, h₁, γ, ha, hb⟩ := h
  refine ⟨z, h₀.trans hx, h₁.trans hy, γ, ?_, ?_⟩
  · have hm := DFunLike.congr_fun
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (KanPath.evaluation X 0) h₀ (𝟙 X) hx (h₀.trans hx)) γ
    simpa only [Category.comp_id, MonoidHom.comp_apply, ha] using hm
  · have hm := DFunLike.congr_fun
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_comp (KanPath.evaluation X 1) h₁ (𝟙 X) hy (h₁.trans hy)) γ
    simpa only [Category.comp_id, MonoidHom.comp_apply, hb] using hm

omit [KanComplex X] in
/-- 指定された path の端点評価は、元の Kan 射の後合成と可換。 -/
lemma path_evaluation_natural {Y : SSet.{u}} (f : X ⟶ Y) (t : Fin 2) :
    (ihom (Δ[1] : SSet.{u})).map f ≫ KanPath.evaluation Y t =
      KanPath.evaluation X t ≫ f := by
  have hu : (ihom (𝟙_ SSet.{u})).map f ≫ (unitIsoSelf (X := Y)).hom =
      (unitIsoSelf (X := X)).hom ≫ f := (unitNatIso (C := SSet.{u})).inv.naturality f
  rw [KanPath.evaluation, KanPath.evaluation, ← Category.assoc,
    (MonoidalClosed.pre (KanPath.endpoint t)).naturality f, Category.assoc, hu,
    Category.assoc]

/-- 元の射を後合成すると、同じ path の像と同じ群の類の像で比較できる。 -/
lemma PiPathRelated.map {Y : SSet.{u}} [KanComplex Y] {n : ℕ}
    {x y : X _⦋0⦌} {a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n x} {b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n y}
    (h : PiPathRelated n a b) (f : X ⟶ Y) :
    PiPathRelated n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl a) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map f rfl b) := by
  obtain ⟨z, h₀, h₁, γ, ha, hb⟩ := h
  let p := (ihom (Δ[1] : SSet.{u})).map f
  let w := p.app (Opposite.op ⦋0⦌) z
  have hw₀ : (KanPath.evaluation Y 0).app _ w = f.app _ x := by
    have h := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) z) (path_evaluation_natural f 0)
    change (KanPath.evaluation Y 0).app _ w = f.app _ ((KanPath.evaluation X 0).app _ z) at h
    simpa only [h₀] using h
  have hw₁ : (KanPath.evaluation Y 1).app _ w = f.app _ y := by
    have h := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) z) (path_evaluation_natural f 1)
    change (KanPath.evaluation Y 1).app _ w = f.app _ ((KanPath.evaluation X 1).app _ z) at h
    simpa only [h₁] using h
  refine ⟨w, hw₀, hw₁, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map p rfl γ, ?_, ?_⟩
  · simpa only [ha] using _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square p f
      (KanPath.evaluation X 0) (KanPath.evaluation Y 0) (path_evaluation_natural f 0)
      rfl rfl h₀ hw₀ n γ
  · simpa only [hb] using _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.HomotopySquares.KanHomotopyGroup.map_square p f
      (KanPath.evaluation X 1) (KanPath.evaluation Y 1) (path_evaluation_natural f 1)
      rfl rfl h₁ hw₁ n γ

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion

module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.FilteredHomotopyRepresentatives
public import SerrePositivity.KST.Spectra.PointedHomotopy
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Filtered.Connected

/-!
概要：点つき Kan 複体の filtered colimit と全自然数次数のホモトピー類の可換性。
方針：代表の有限段での実現と等式の後続段での実現から型の余極限の普遍性を証明する。
規約：零次数を含む集合としての比較。正次数の群構造との整合は別に束ねる。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。L9d の telescope の計算。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：誘導写像の二つの値の一致は像の基点の等しい表示に依存しない。
方針：二つの基点保存式で等式帰納する。
規約：定義域の基点と二つの元は固定する。
使われ方：Goerss–Jardine I §7。余極限の基点を各段の像と合わせる。 -/
theorem KanHomotopy.map_eq_iff_basepoint {X Y : SSet.{u}} [KanComplex X] [KanComplex Y]
    {x : X _⦋0⦌} {y z : Y _⦋0⦌} (n : ℕ) (f : X ⟶ Y)
    (hy : f.app _ x = y) (hz : f.app _ x = z) (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy X n x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f hy a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f hy b ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f hz a = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f hz b := by
  subst y
  subst z
  rfl

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (D : J ⥤ PointedSimplicialSet.{u}) [∀ j, KanComplex (D.obj j).right]

/-- 概要：点つき単体集合の filtered diagram は余極限を持つ。
方針：filtered 圏の連結性と under 圏の連結余極限を使う。
規約：各段の Kan 性はこの存在には不要。
使われ方：Goerss–Jardine I §7、HA §1.4.2。filtered Kan 余極限の点つき対象。 -/
instance pointedFilteredDiagram_hasColimit : HasColimit D := by
  let : IsConnected J := IsFiltered.isConnected J
  infer_instance

/-- 概要：基点忘却は点つき filtered diagram の余極限を保存する。
方針：filtered 圏の連結性と under 圏の忘却の連結余極限保存を使う。
規約：各段の Kan 性は不要。
使われ方：Goerss–Jardine I §7、HA §1.4.2。基礎単体集合の colimit との比較。 -/
instance pointedFilteredDiagram_preservesColimit :
    PreservesColimit D PointedSimplicialSet.forget := by
  let : IsConnected J := IsFiltered.isConnected J
  infer_instance

/-- 概要：点つき Kan 複体の図式に各自然数次数のホモトピー類を施した図式。
方針：各段の基点で取り、点つき射の誘導写像を使う。
規約：値域は型の圏。零次数の群構造を仮定しない。
使われ方：Goerss–Jardine I §7、HA §1.4.2。π_n の filtered colimit の図式。 -/
def pointedHomotopyDiagram (n : ℕ) : J ⥤ Type u where
  obj j := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (D.obj j).right n (D.obj j).basepoint
  map f := ↾(pointedHomotopyMap n (D.map f))
  map_id j := by
    ext a
    change pointedHomotopyMap n (D.map (𝟙 j)) a = a
    rw [D.map_id]
    exact pointedHomotopyMap_id _ n a
  map_comp f g := by
    ext a
    change pointedHomotopyMap n (D.map (f ≫ g)) a =
      pointedHomotopyMap n (D.map g) (pointedHomotopyMap n (D.map f) a)
    rw [D.map_comp]
    exact pointedHomotopyMap_comp n _ _ a

/-- 概要：点つき Kan 複体の filtered diagram の点つき余極限も Kan。
方針：基点忘却が連結余極限を保存することと有限ホーンの充填を使う。
規約：遷移射の単射性を要求しない。
使われ方：Goerss–Jardine I §7、BF 1978 §2。telescope の各段の比較対象。 -/
instance pointedFilteredColimit_kanComplex : KanComplex (colimit D).right := by
  let : ∀ j, KanComplex ((D ⋙ PointedSimplicialSet.forget).obj j) :=
    fun j ↦ inferInstanceAs (KanComplex (D.obj j).right)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanComplex_of_filtered_isColimit
    (isColimitOfPreserves PointedSimplicialSet.forget (colimit.isColimit D))

variable {D} (c : Cocone D) [KanComplex c.pt.right]

/-- 概要：点つき cocone の各自然数次数のホモトピー類の cocone。
方針：各 cocone 射の誘導写像を脚に取る。
規約：極限や同値を仮定せず、通常の cocone として作る。
使われ方：Goerss–Jardine I §7、HA §1.4.2。π_n の余極限の普遍性。 -/
def pointedHomotopyCocone (n : ℕ) : Cocone (pointedHomotopyDiagram D n) where
  pt := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy c.pt.right n c.pt.basepoint
  ι := {
    app j := ↾(pointedHomotopyMap (Y := c.pt) n (c.ι.app j))
    naturality j k f := by
      ext a
      change pointedHomotopyMap (Y := c.pt) n (c.ι.app k) (pointedHomotopyMap n (D.map f) a) =
        pointedHomotopyMap (Y := c.pt) n (c.ι.app j) a
      rw [← pointedHomotopyMap_comp (Z := c.pt), c.w f] }

variable (hc : IsColimit (PointedSimplicialSet.forget.mapCocone c))

include hc in
/-- 概要：点つき余極限のホモトピー類は一つの段から来る。
方針：有限な代表単体を下ろし、基点の像の等式による移送で点つき代表へ戻す。
規約：全自然数次数で有効。
使われ方：Goerss–Jardine I §7、HA §1.4.2。π_n の余極限比較の全射性。 -/
theorem pointedHomotopyCocone_surjective (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy c.pt.right n c.pt.basepoint) :
    ∃ (j : J) (b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (D.obj j).right n (D.obj j).basepoint),
      pointedHomotopyMap (Y := c.pt) n (c.ι.app j) b = a := by
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  obtain ⟨s, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FromTopologicalSpacesToSimplicialSets.KanHomotopy.mk_surjective n a
  let s' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (𝟙 c.pt.right) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (c.ι.app j)).symm s
  obtain ⟨k, v, t, ht⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.ptSimplex_filtered_factorization hc j (D.obj j).basepoint n s'
  let t' := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (𝟙 (D.obj k).right) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (D.map v)) t
  refine ⟨k, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n t', ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map (Y := c.pt.right) n (c.ι.app k).right _ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.mk n t') = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_mk]
  congr 1
  apply RelativeMorphism.ext
  change t.map ≫ (c.ι.app k).right = s'.map at ht
  simpa only [s', t', _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex_map, Category.id_comp, Category.comp_id] using ht

include hc in
/-- 概要：同じ段の点つきホモトピー類の像が余極限で一致すれば後続段で一致する。
方針：基点の表示を合わせて RelStruct の有限段での実現を適用する。
規約：全自然数次数で有効。
使われ方：Goerss–Jardine I §7、HA §1.4.2。π_n の余極限比較の単射性。 -/
theorem pointedHomotopyCocone_eq_eventually (n : ℕ) (j : J)
    (a b : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy (D.obj j).right n (D.obj j).basepoint)
    (h : pointedHomotopyMap (Y := c.pt) n (c.ι.app j) a =
      pointedHomotopyMap (Y := c.pt) n (c.ι.app j) b) :
    ∃ (k : J) (v : j ⟶ k),
      pointedHomotopyMap n (D.map v) a = pointedHomotopyMap n (D.map v) b := by
  have h' := (KanHomotopy.map_eq_iff_basepoint (Y := c.pt.right) n (c.ι.app j).right
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) rfl a b).1 h
  let : ∀ j, KanComplex ((D ⋙ PointedSimplicialSet.forget).obj j) :=
    fun j ↦ inferInstanceAs (KanComplex (D.obj j).right)
  let : KanComplex (PointedSimplicialSet.forget.mapCocone c).pt :=
    inferInstanceAs (KanComplex c.pt.right)
  obtain ⟨k, v, hv⟩ := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.homotopy_filtered_eq_eventually hc j n a b h'
  refine ⟨k, v, ?_⟩
  exact (KanHomotopy.map_eq_iff_basepoint n (D.map v).right rfl
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint _) a b).1 hv

include hc in
/-- 概要：点つき Kan 複体の filtered colimit に π_n を施した cocone は余極限。
方針：代表の全射性と等式の後続段での実現による型の余極限判定を使う。
規約：零次数を含む全自然数次数について集合として主張する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。L9d の π_* 計算。 -/
def pointedHomotopyIsColimit (n : ℕ) : IsColimit (pointedHomotopyCocone c n) :=
  Types.FilteredColimit.isColimitOf' (pointedHomotopyDiagram D n)
    (pointedHomotopyCocone c n)
    (fun a ↦ by
      obtain ⟨j, b, hb⟩ := pointedHomotopyCocone_surjective c hc n a
      exact ⟨j, b, hb.symm⟩)
    (fun j a b h ↦ pointedHomotopyCocone_eq_eventually c hc n j a b h)

end

end SerrePositivity.KST.Spectra

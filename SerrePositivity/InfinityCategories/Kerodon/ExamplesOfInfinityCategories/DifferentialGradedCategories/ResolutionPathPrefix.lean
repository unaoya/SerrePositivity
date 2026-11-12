module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ResolutionHomValue

/-!
# 解像の引き戻しで除く Path の先頭部分

概要：始点を変える引き戻しで、除かれる先頭部分を先頭面内の Path の旗として構成する。
方針：各有限集合を新しい始点以下に制限し、持ち上げた像が native な prefix に等しいと示す。
規約：先頭面は最終頂点を除いた元の n 単体である。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の定値先頭面の単位保存による自然性。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening
open scoped _root_.Simplicial

/-- 概要：解像の各段の新しい始点以下の点から先頭面内の Path を作る。
方針：元の始点と最初に選んだ段の最大元が全ての後の段に属することを使う。
規約：最終頂点を加える前の Fin(n+1) を使う。
使われ方：Kerodon 2.5.9（Tag 00SC） の切り落とす先頭部分の豊穣写像の計算。 -/
def resolutionFlagFrontPath {n d e : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (t : Fin (e + 1)) :
    SimplicialThickening.Path (ULift.up F.start : ULift.{u} (Fin (n + 1)))
      (ULift.up (F.maxAt (α 0))) where
  I := {z | z.down ∈ F.sets (α t) ∧ z.down ≤ F.maxAt (α 0)}
  left := ⟨F.start_mem _, F.lower _ _ (F.maxAt_mem (α 0))⟩
  right := ⟨F.monotone_sets (α.monotone (Fin.zero_le t)) (F.maxAt_mem (α 0)), le_rfl⟩
  left_le _ hz := F.lower _ _ hz.1
  le_right _ hz := hz.2

/-- 概要：解像の先頭部分の各段は先頭面内の Path の単体になる。
方針：有限集合の包含を切断後の Path の包含へ写す。
規約：切断点は全段で固定する。
使われ方：HA 1.3.1.17 の先頭面が定値である条件を評価する入力。 -/
def resolutionFlagFrontFunctor {n d e : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) :
    (nerve (SimplicialThickening.Path (ULift.up F.start : ULift.{u} (Fin (n + 1)))
      (ULift.up (F.maxAt (α 0))))) _⦋e⦌ where
  obj := resolutionFlagFrontPath F α
  map f := ⟨⟨⟨fun _ h ↦ ⟨F.monotone_sets (α.monotone f.le) h.1, h.2⟩⟩⟩⟩
  map_id _ := InducedCategory.hom_ext (Subsingleton.elim _ _)
  map_comp _ _ := InducedCategory.hom_ext (Subsingleton.elim _ _)

/-- 概要：先頭面内で作った Path の像は元の Path の新しい始点までの前半である。
方針：持ち上げた像の所属を比較し、最後の頂点が切断点以下にはならないことを使う。
規約：先頭面の包含は castSucc の持ち上げである。
使われ方：Kerodon 2.5.9（Tag 00SC） の Path の分解と定値先頭面の接続。 -/
lemma resolutionFlagFrontPath_image {n d e : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (t : Fin (e + 1)) :
    (SimplicialThickening.functorMap Fin.castSuccOrderEmb.toOrderHom.uliftMap
      (.mk (ULift.up F.start)) (.mk (ULift.up (F.maxAt (α 0))))).obj
        (resolutionFlagFrontPath.{u} F α t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathPrefix (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath F (α t))
        (ULift.up (F.maxAt (α 0)).castSucc) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath_cut_mem F α t) := by
  apply CategoryTheory.SimplicialThickening.Path.ext
  apply Set.ext
  intro z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨Or.inr ⟨w.down, hw.1, rfl⟩, hw.2⟩
  · rintro ⟨hz, hle⟩
    rcases hz with hz | ⟨j, hj, rfl⟩
    · have hlast : Fin.last (n + 1) ≤ (F.maxAt (α 0)).castSucc := by
        have hz' : z.down = Fin.last (n + 1) :=
          congrArg ULift.down (Set.mem_singleton_iff.mp hz)
        change z.down ≤ (F.maxAt (α 0)).castSucc at hle
        rw [hz'] at hle
        exact hle
      exact False.elim ((not_le_of_gt (Fin.castSucc_lt_last _)) hlast)
    · exact ⟨ULift.up j, ⟨hj, hle⟩, rfl⟩

/-- 概要：先頭面の Path の像と引き戻した旗の Path の合成は元の選んだ Path である。
方針：前半と末尾への同定の後に native な Path の分解の等式を使う。
規約：合成は Mathlib の通常の順序で前半から後半へ進む。
使われ方：HA 1.3.1.17 の解像での評価の面・退化との可換性。 -/
lemma resolutionFlagPath_decomposition {n d e : ℕ} (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d)
    (α : Fin (e + 1) →o Fin (d + 1)) (t : Fin (e + 1)) :
    (SimplicialThickening.compFunctor
      (.mk (ULift.up F.start.castSucc : ULift.{u} (Fin (n + 2))))
      (.mk (ULift.up (F.maxAt (α 0)).castSucc)) (.mk (ULift.up (Fin.last (n + 1))))).obj
      (((SimplicialThickening.functorMap Fin.castSuccOrderEmb.toOrderHom.uliftMap
        (.mk (ULift.up F.start)) (.mk (ULift.up (F.maxAt (α 0))))).obj
          (resolutionFlagFrontPath F α t)), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath (F.pullback α) t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath F (α t) := by
  rw [resolutionFlagFrontPath_image, ← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath_pullback F α t]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathPrefix_comp_pathSuffix (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath.{u} F (α t))
    (ULift.up (F.maxAt (α 0)).castSucc) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.resolutionFlagPath_cut_mem F α t)

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
